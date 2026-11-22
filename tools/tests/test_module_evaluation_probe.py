"""The linked-leaf observer retains failures and compares full resumed state."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
from evaluation import module_profile


class ModuleEvaluationProbe(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.probe=shutil.which(os.environ.get('NIRVANA_MODULE_PROBE','/nonexistent/module-probe'))
        if not cls.probe or not shutil.which('cc'): raise unittest.SkipTest('requires compiled module probe and C compiler')

    def build(self,root,body):
        source=root/'input.S';driver=root/'driver.c';elf=root/'input.elf';oracle=root/'native'
        source.write_text('.text\n.global fixture\n.type fixture,@function\nfixture:\n'+body+
                          '\n.size fixture,.-fixture\n.section .note.GNU-stack,"",@progbits\n')
        driver.write_text('int main(void){return 0;}\n')
        for main,target in [(driver,elf),(ROOT/'tests/fixtures/harness.c',oracle)]:
            subprocess.run(['cc','-no-pie','-Wl,--build-id=none',str(source),str(main),'-o',str(target)],
                           check=True,capture_output=True,timeout=30)
        return elf,oracle

    def run_probe(self,root,elf,oracle=None):
        inputs=root/'inputs.txt';inputs.write_text('1 2 3 4\n');out=root/'evidence'
        args=[self.probe,'--module',str(elf),str(inputs),str(out)]
        if oracle is not None: args.append(str(oracle))
        result=subprocess.run(args,capture_output=True,text=True,timeout=60)
        self.assertEqual(result.returncode,0,result.stderr)
        report=json.loads(result.stdout)
        self.assertEqual(report,json.loads((out/'report.json').read_text()))
        self.assertEqual(report['requested_vectors'],1)
        self.assertEqual((out/'input.elf').read_bytes(),elf.read_bytes())
        return report,out

    def test_native_full_ram_and_every_resumption_budget_use_distinct_contract_fields(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);elf,oracle=self.build(root,'pxor %xmm0,%xmm0\nmovq %xmm0,%rax\nret')
            report,out=self.run_probe(root,elf,oracle)
            self.assertEqual(report['status'],'passed')
            self.assertEqual(report['native_compared'],1)
            self.assertGreater(report['resumption_cases'],0)
            self.assertEqual(report['generated_compared'],report['cases']*6)
            self.assertEqual(report['checked_ram_bytes'],report['generated_compared']*report['memory_size'])
            self.assertEqual(len((out/'expected.tsv').read_text().splitlines()),report['cases'])
            self.assertEqual((out/'native-observed.tsv').read_text().split(),['0','1','2','3','4'])
            replayed=module_profile.replay(out)
            self.assertEqual(replayed['generated_rows'],report['generated_compared'])
            observed=out/'core-O0-64.observed.tsv';saved=observed.read_text()
            observed.write_text('1'+saved[1:])
            with self.assertRaisesRegex(ValueError,'generated observations'): module_profile.replay(out)
            observed.write_text(saved)
            memory=out/'memory-0000.bin';saved=memory.read_bytes()
            memory.write_bytes(bytes([saved[0]^1])+saved[1:])
            with self.assertRaisesRegex(ValueError,'RAM digest'): module_profile.replay(out)

    def test_decode_and_oracle_failures_keep_the_requested_denominator(self):
        for variant in ['unsupported','bad-oracle']:
            with self.subTest(variant=variant),tempfile.TemporaryDirectory() as directory:
                root=Path(directory);elf,_=self.build(root,'ud2' if variant=='unsupported' else 'xor %eax,%eax\nret')
                report,_=self.run_probe(root,elf,None if variant=='unsupported' else root/'missing-oracle')
                self.assertEqual(report['status'],'unsupported' if variant=='unsupported' else 'evaluator_error')
                self.assertTrue(report['reason'])
