import io
import json
from pathlib import Path
import tempfile
import unittest
from compact_legacy_cache import compact_stream, verify_stream, convert
from lean_build_cache import unpack_record, provenance_equal


class CompactLegacyTests(unittest.TestCase):
    def test_exact_roundtrip_with_shared_and_scalar_values(self):
        value = {'hash': 'abc', 'values': [None, True, False, 1, 1.0, -0.0, 'é', {'ref': 12}]}
        for _ in range(10):
            value = {'imports': [value, value]}
        raw = json.dumps({'schema': 1, 'inputs': value}).encode()
        packed = compact_stream(io.BytesIO(raw))
        verify_stream(io.BytesIO(raw), packed)
        self.assertTrue(provenance_equal(unpack_record(packed), json.loads(raw)))
        self.assertLess(len(json.dumps(packed)), len(raw) // 10)

    def test_detects_corruption_and_order_changes(self):
        raw = b'{"schema":1,"a":[1,2],"b":true}'
        for other in [b'{"schema":1,"a":[1,3],"b":true}',
                      b'{"schema":1,"b":true,"a":[1,2]}',
                      b'{"schema":1,"a":[1,2],"b":1}']:
            with self.assertRaises(ValueError):
                verify_stream(io.BytesIO(raw), compact_stream(io.BytesIO(other)))

    def test_rejects_duplicate_keys(self):
        with self.assertRaises(ValueError):
            compact_stream(io.BytesIO(b'{"schema":1,"schema":2}'))

    def test_atomic_conversion_is_idempotent(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'record.json'
            value = {'schema': 1, 'inputs': {'source_sha256': 'abc'}}
            path.write_text(json.dumps(value))
            result = convert(path)
            self.assertTrue(result['exact_event_roundtrip'])
            self.assertEqual(unpack_record(json.loads(path.read_text())), value)
            self.assertIsNone(convert(path))


if __name__ == '__main__':
    unittest.main()
