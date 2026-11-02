"""Regression checks for lossless storage of shared build provenance."""
import gzip
import json
from pathlib import Path
import tempfile
import unittest
from lean_build_cache import Config, atomic_json, load_record, pack_record, unpack_record, provenance_equal


class SharedRecordTests(unittest.TestCase):
    def test_shared_graph_roundtrip_and_size(self):
        value = {'source_sha256': 'abc', 'scalar_values': [None, True, 1, 'ref']}
        for _ in range(20):
            value = {'imports': [value, value]}
        record = {'schema': 1, 'inputs': value, 'compiler_output': 'checked'}
        encoded = json.dumps(pack_record(record))
        decoded = unpack_record(json.loads(encoded))
        self.assertEqual(decoded, record)
        self.assertIs(decoded['inputs']['imports'][0], decoded['inputs']['imports'][1])
        self.assertLess(len(encoded), 12000)

    def test_changes_remain_visible(self):
        original = {'schema': 1, 'inputs': {'source_sha256': 'abc', 'imports': []}}
        changed = unpack_record(json.loads(json.dumps(pack_record(original))))
        changed['inputs']['source_sha256'] = 'different'
        self.assertNotEqual(changed, original)

    def test_literal_reference_fields_are_not_special(self):
        record = {'schema': 1, 'inputs': {'ref': 0, 'nodes': ['dict', 'list']}}
        self.assertEqual(unpack_record(pack_record(record)), record)

    def test_malformed_references_and_cycles_rejected(self):
        for ref, nodes in [(-1, []), (True, []), (0, [['list', [{'ref': 0}]]])]:
            with self.assertRaises(ValueError):
                unpack_record({'record_encoding': 'shared-json-v1',
                               'root': {'ref': ref}, 'nodes': nodes})

    def test_legacy_compressed_and_new_loading(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            config = Config(root, Path('/bin/true'), [], {})
            config.initialize()
            output = root / 'test.olean'
            path = config.record_path(output)
            record = {'schema': 1, 'inputs': {'source_sha256': 'abc'},
                      'compiler_output': 'checked'}
            path.write_text(json.dumps(record))
            self.assertEqual(load_record(config, output), record)
            with gzip.open(str(path) + '.gz', 'wt') as stream:
                json.dump(record, stream)
            path.unlink()
            self.assertEqual(load_record(config, output), record)
            atomic_json(path, record)
            self.assertEqual(load_record(config, output), record)
            self.assertEqual(json.loads(path.read_text())['record_encoding'], 'shared-json-v1')



class ProvenanceEqualityTests(unittest.TestCase):
    def test_deep_shared_dag_and_deep_changed_hash(self):
        left_leaf = {'source_sha256': 'abc', 'artifact_sha256': 'def'}
        right_leaf = dict(left_leaf)
        left, right = left_leaf, right_leaf
        for _ in range(2000):
            left, right = {'imports': [left, left]}, {'imports': [right, right]}
        self.assertTrue(provenance_equal(left, right))
        right_leaf['artifact_sha256'] = 'changed'
        self.assertFalse(provenance_equal(left, right))
        right_leaf['artifact_sha256'] = 'def'
        self.assertTrue(provenance_equal(left, right))
        right_leaf['source_sha256'] = 'changed'
        self.assertFalse(provenance_equal(left, right))

    def test_sharing_is_not_part_of_value(self):
        leaf = {'hash': ['abc']}
        self.assertTrue(provenance_equal([leaf, leaf],
                                       [{'hash': ['abc']}, {'hash': ['abc']}]))
        self.assertTrue(provenance_equal({'a': 1, 'b': 2}, {'b': 2, 'a': 1}))

    def test_shape_order_and_companions(self):
        for left, right in [([1, 2], [2, 1]), ([1], [1, 2]),
                            ({'a': 1}, {'b': 1}), ({}, []), ([], None),
                            ({'output_companions': {'.private': 'abc'}},
                             {'output_companions': {'.private': 'def'}})]:
            self.assertFalse(provenance_equal(left, right))
            self.assertFalse(provenance_equal(right, left))

    def test_matches_builtin_on_small_random_json(self):
        import random
        rng = random.Random(57)
        def value(depth):
            if depth == 0 or rng.randrange(3) == 0:
                return rng.choice([None, True, False, 0, 1, 2, 'hash', 'other'])
            if rng.randrange(2):
                return [value(depth - 1) for _ in range(rng.randrange(4))]
            return {str(i): value(depth - 1) for i in range(rng.randrange(4))}
        for _ in range(500):
            left, right = value(4), value(4)
            self.assertEqual(provenance_equal(left, right), left == right)
            copy = json.loads(json.dumps(left))
            self.assertEqual(provenance_equal(left, copy), left == copy)


if __name__ == '__main__':
    unittest.main()
