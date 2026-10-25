# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Safe witness YAML IO, with optional LibYAML acceleration.

Both backends enforce the same duplicate-key and timestamp rules. Schema
validation stays with the caller; using LibYAML does not bypass it.
"""
from pathlib import Path


def yaml_module():
    try:
        import yaml
        return yaml
    except ImportError as error:
        raise ValueError("install scripts/requirements-witness.txt for YAML witness IO") from error


def _base(yaml, kind, backend):
    if backend not in {"auto", "python", "c"}:
        raise ValueError(f"unknown YAML backend: {backend}")
    accelerated = getattr(yaml, "CSafe" + kind, None)
    if backend == "c" and accelerated is None:
        raise ValueError("LibYAML is not available")
    return accelerated if backend != "python" and accelerated else getattr(yaml, "Safe" + kind)


def load(stream, *, backend="auto"):
    yaml = yaml_module()
    base = _base(yaml, "Loader", backend)

    class WitnessLoader(base):
        pass

    # YAML 1.2 timestamps remain strings. Copy the resolver table so ordinary
    # PyYAML clients in the same process retain their original behavior.
    WitnessLoader.yaml_implicit_resolvers = {
        key: [(tag, expression) for tag, expression in values
              if tag != "tag:yaml.org,2002:timestamp"]
        for key, values in base.yaml_implicit_resolvers.items()
    }

    def unique_mapping(loader, node, deep=False):
        loader.flatten_mapping(node)
        result = {}
        for key_node, value_node in node.value:
            key = loader.construct_object(key_node, deep=deep)
            if not isinstance(key, (str, int, float, bool)):
                raise ValueError("witness mapping keys must be scalar")
            if key in result:
                raise ValueError(f"duplicate YAML witness key: {key}")
            result[key] = loader.construct_object(value_node, deep=deep)
        return result

    WitnessLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping)
    try:
        return yaml.load(stream, Loader=WitnessLoader)
    except yaml.YAMLError as error:
        raise ValueError(f"invalid YAML witness: {error}") from error


def load_file(path, *, backend="auto"):
    with Path(path).open(encoding="utf-8") as stream:
        return load(stream, backend=backend)


def dump(value, stream=None, *, backend="auto", allow_unicode=True):
    yaml = yaml_module()
    base = _base(yaml, "Dumper", backend)

    class WitnessDumper(base):
        def ignore_aliases(self, data):
            # CPAchecker's waypoint importer requires independent location
            # mappings; shared Python dictionaries must not produce YAML aliases.
            return True

    return yaml.dump(value, stream, Dumper=WitnessDumper, sort_keys=False,
                     allow_unicode=allow_unicode)
