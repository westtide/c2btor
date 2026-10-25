"""Keep accelerated and portable witness IO equivalent and strict."""
import datetime
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts import yaml_io


def check_schema(document, name="violation-witness-schema.yml"):
    """Test-only official YAML 2.1 schema check, with pinned local schemas."""
    from jsonschema import validators, FormatChecker
    from referencing import Registry, Resource
    from referencing.jsonschema import DRAFT202012
    from scripts.source_map import digest
    directory = Path(__file__).resolve().parent / "schema"
    lock = json.loads((directory / "source.json").read_text())
    names = [name, "common/location.yml", "common/metadata.yml"]
    for filename in names:
        if digest(directory / filename) != lock["sha256"][filename]:
            raise ValueError("official schema hash mismatch: " + filename)
    schema, *common = [yaml_io.load_file(directory / filename) for filename in names]
    registry = Registry()
    for value in common:
        registry = registry.with_resource(value["$id"], Resource.from_contents(value, default_specification=DRAFT202012))
    validators.validator_for(schema)(schema, registry=registry, format_checker=FormatChecker()).validate(document)


class WitnessYamlIOTests(unittest.TestCase):
    def backends(self):
        return ["python", "auto"]

    def test_strings_and_c_constraints_round_trip(self):
        strings = ["2.1", "1", "true", "false", "yes", "no", "null", "~",
                   "0x10", "01", ".nan", ".inf", "2026-10-17T00:00:00Z",
                   "\u7a0b\u5e8f.c", "line\nnext", "quote'\"", "slash\\tab\t",
                   r"\result == (-9223372036854775807LL - 1LL)",
                   r"\result <= 0.0f && \result >= 0.0f"]
        value = {"strings": strings, "bool": True, "number": 7, "empty": None}
        for writer in self.backends():
            stream = io.StringIO()
            self.assertIsNone(yaml_io.dump(value, stream, backend=writer))
            for reader in self.backends():
                with self.subTest(writer=writer, reader=reader):
                    self.assertEqual(yaml_io.load(io.StringIO(stream.getvalue()), backend=reader), value)

    def test_timestamp_stays_string_without_changing_pyyaml(self):
        yaml = yaml_io.yaml_module()
        text = "creation_time: 2026-10-17T00:00:00Z\n"
        for backend in self.backends():
            self.assertIsInstance(yaml_io.load(text, backend=backend)["creation_time"], str)
        self.assertIsInstance(yaml.safe_load(text)["creation_time"], datetime.datetime)

    def test_duplicate_mapping_keys_fail_with_both_backends(self):
        texts = ["type: target\ntype: function_return\n",
                 "metadata:\n  format_version: '2.1'\n  format_version: '2.0'\n",
                 "base: &b {line: 1}\nlocation: {<<: *b, line: 2}\n",
                 "true: one\n1: two\n"]
        for backend in self.backends():
            for text in texts:
                with self.subTest(backend=backend, text=text), self.assertRaisesRegex(ValueError, "duplicate YAML witness key"):
                    yaml_io.load(text, backend=backend)

    def test_unsafe_tags_and_nonscalar_keys_fail(self):
        for backend in self.backends():
            for text in ("!!python/object/new:object []", "? [a, b]\n: value\n"):
                with self.subTest(backend=backend, text=text), self.assertRaises(ValueError):
                    yaml_io.load(text, backend=backend)

    def test_shared_locations_never_create_aliases(self):
        location = {"file_name": "source.c", "line": 4, "column": 8}
        value = [{"waypoint": {"location": location}}, {"waypoint": {"location": location}}]
        for backend in self.backends():
            text = yaml_io.dump(value, backend=backend)
            self.assertNotIn("&id", text)
            self.assertNotIn("*id", text)
            parsed = yaml_io.load(text, backend=backend)
            self.assertEqual(parsed, value)
            self.assertIsNot(parsed[0]["waypoint"]["location"], parsed[1]["waypoint"]["location"])

    def test_optional_libyaml_falls_back_to_safe_python(self):
        yaml = yaml_io.yaml_module()
        with patch.object(yaml, "CSafeLoader", None, create=True), patch.object(yaml, "CSafeDumper", None, create=True):
            text = yaml_io.dump({"format_version": "2.1", "value": "1"})
            self.assertEqual(yaml_io.load(text), {"format_version": "2.1", "value": "1"})
            with self.assertRaisesRegex(ValueError, "duplicate"):
                yaml_io.load("a: 1\na: 2\n")

    def test_file_loading_uses_utf8_and_preserves_strings(self):
        value = {"file_name": "\u76ee\u5f55/\u7a0b\u5e8f.c", "value": "1"}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "witness.yml"
            with path.open("w", encoding="utf-8") as stream:
                yaml_io.dump(value, stream)
            self.assertEqual(yaml_io.load_file(path), value)

    def test_sample_order_survives_accelerated_io(self):
        value = [{"value": rf"\result == {i % 3}", "line": i + 1} for i in range(1000)]
        for backend in self.backends():
            parsed = yaml_io.load(yaml_io.dump(value, backend=backend), backend=backend)
            self.assertEqual(parsed, value)


if __name__ == "__main__":
    unittest.main()
