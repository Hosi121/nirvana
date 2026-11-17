"""Keep output-size observations stable when declaration placement changes."""

import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "compare_readable_output", Path(__file__).resolve().parents[1] / "compare_readable_output.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class DeclarationMetrics(unittest.TestCase):
    def test_initializers_preserve_local_role_and_copy_counts(self):
        before = """uint64_t nirvana_readable(uint64_t arg0) {
    uint64_t counter;
    uint8_t value;
    uint32_t accumulator;
    counter = arg0;
    value = counter;
    accumulator = value;
    return accumulator;
}
"""
        after = """uint64_t nirvana_readable(uint64_t arg0) {
    uint64_t counter = arg0;
    uint8_t value = counter;
    uint32_t accumulator = value;
    return accumulator;
}
"""
        old, new = MODULE.metrics(before), MODULE.metrics(after)
        for key, expected in [("locals", 3), ("named_roles", 2), ("copies", 2)]:
            self.assertEqual(old[key], expected)
            self.assertEqual(new[key], expected)
        self.assertEqual(old["initialized_locals"], 0)
        self.assertEqual(new["initialized_locals"], 3)
        self.assertLess(new["tokens"], old["tokens"])

    def test_only_function_storage_declarations_contribute(self):
        code = """static inline uint64_t helper(uint64_t value) {
    uint64_t counter = value;
    return counter;
}
uint64_t nirvana_readable(uint64_t arg0) {
    /* uint64_t address = arg0; */
    // uint64_t accumulator;
    uint16_t limit = 7;
    uint64_t nirvana_ordered_0 = arg0;
    return limit + nirvana_ordered_0;
}
"""
        result = MODULE.metrics(code)
        self.assertEqual(result["locals"], 1)
        self.assertEqual(result["named_roles"], 1)
        self.assertEqual(result["initialized_locals"], 1)


if __name__ == "__main__":
    unittest.main()
