"""Retained binaries report their build's source, including Cargo rebuilds."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from evaluation import build_identity

ROOT=Path(__file__).resolve().parents[2]


class BuildIdentityFormat(unittest.TestCase):
    def test_unknown_and_legacy_versions_are_explicit(self):
        for text,revision,dirty in [('nirvana 0.1.0 git=unknown source_dirty=unknown',None,None),
                                    ('nirvana 0.1.0 git='+'1'*40+' source_dirty=false','1'*40,False)]:
            result=build_identity.parse(dict(version=text,returncode=0))
            self.assertEqual(result['source_revision'],revision)
            self.assertIs(result['source_dirty'],dirty)
        for tool in [{},dict(version=None,returncode=0),dict(version='old nirvana',returncode=0),
                     dict(version=text,returncode=True),dict(version=text+'\nextra',returncode=0)]:
            self.assertIsNone(build_identity.parse(tool))


class CargoBuildIdentity(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not shutil.which('cargo') or not shutil.which('git'): raise unittest.SkipTest('requires Cargo and Git')

    def command(self,root,*args,env=None):
        result=subprocess.run(args,cwd=root,env=env,capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        return result.stdout.strip()

    def package(self,root):
        root.mkdir(parents=True,exist_ok=True);(root/'src').mkdir()
        (root/'Cargo.toml').write_text('[package]\nname="identity-probe"\nversion="0.1.0"\nedition="2024"\n')
        shutil.copyfile(ROOT/'build.rs',root/'build.rs')
        (root/'src/main.rs').write_text('fn main(){println!("{} {}",env!("NIRVANA_BUILD_REVISION"),env!("NIRVANA_SOURCE_DIRTY"));}\n')

    def build(self,root):
        env={**os.environ,'CARGO_TARGET_DIR':str(root/'target')}
        return self.command(root,'cargo','run','--quiet','--offline',env=env).split()

    def commit(self,root):
        self.command(root,'git','add','src','Cargo.toml','Cargo.lock','build.rs')
        self.command(root,'git','-c','core.hooksPath=/dev/null','-c','commit.gpgsign=false',
                     '-c','user.name=Build identity test','-c','user.email=identity@example.invalid','commit','--quiet','-m','fixture')
        return self.command(root,'git','rev-parse','HEAD')

    def test_cargo_refreshes_commits_and_source_edits_and_handles_archives_and_worktrees(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)/'checkout';self.package(root)
            self.command(root,'git','init','--quiet','--initial-branch=main')
            self.assertEqual(self.build(root),['unknown','true'])
            revision=self.commit(root)
            self.assertEqual(self.build(root),[revision,'false'])
            main=root/'src/main.rs';main.write_text(main.read_text()+'\n')
            self.assertEqual(self.build(root),[revision,'true'])
            newer=self.commit(root);self.assertNotEqual(newer,revision)
            # Git updates may carry older mtimes after clock adjustments. The
            # build identity must reflect the new contents, not cached env vars.
            for relative in ['HEAD','index','refs','refs/heads','refs/heads/main']:
                os.utime(root/'.git'/relative,ns=(1,1))
            self.assertEqual(self.build(root),[newer,'false'])
            self.command(root,'git','pack-refs','--all','--prune')
            self.assertEqual(self.build(root),[newer,'false'])
            archive=root/'archive';self.package(archive)
            self.assertEqual(self.build(archive),['unknown','unknown'])
            worktree=Path(directory)/'detached'
            self.command(root,'git','worktree','add','--detach',str(worktree),revision)
            try: self.assertEqual(self.build(worktree),[revision,'false'])
            finally:
                shutil.rmtree(worktree/'target',ignore_errors=True)
                self.command(root,'git','worktree','remove',str(worktree))
