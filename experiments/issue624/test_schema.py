"""Reject drift in either generated prover description and retain proof tails."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from experiments.issue624 import generate_schema


class SchemaGeneratorTests(unittest.TestCase):
    def test_checked_in_descriptions_match_shared_generator(self):
        generate_schema.generate(check=True)

    def test_editing_either_prover_is_detected_and_repaired(self):
        for language, extension in (("lean", "lean"), ("rocq", "v")):
            with self.subTest(
                language=language
            ), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                with patch.object(generate_schema, "ROOT", root):
                    for prover, suffix in (("lean", "lean"), ("rocq", "v")):
                        path = (
                            root
                            / f"proofs/experiments/issue624/{prover}/Schema.{suffix}"
                        )
                        path.parent.mkdir(parents=True)
                    generate_schema.generate()
                    generate_schema.generate(check=True)
                    path = (
                        root
                        / f"proofs/experiments/issue624/{language}/Schema.{extension}"
                    )
                    original = path.read_text()
                    constructor = ".const 4" if language == "lean" else "EConst 4"
                    self.assertIn(constructor, original)
                    path.write_text(
                        original.replace(constructor, constructor[:-1] + "5", 1)
                    )
                    with self.assertRaisesRegex(SystemExit, f"{language}/Schema"):
                        generate_schema.generate(check=True)
                    generate_schema.generate()
                    self.assertEqual(path.read_text(), original)

    def test_regeneration_preserves_prover_specific_proofs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(generate_schema, "ROOT", root):
                for language, extension in (("lean", "lean"), ("rocq", "v")):
                    path = (
                        root
                        / f"proofs/experiments/issue624/{language}/Schema.{extension}"
                    )
                    path.parent.mkdir(parents=True)
                    tail = f"\nProof tail for {language}.\n"
                    path.write_text(
                        "stale data\n" + generate_schema.MARKERS[language] + tail
                    )
                generate_schema.generate()
                generate_schema.generate(check=True)
                for language, extension in (("lean", "lean"), ("rocq", "v")):
                    path = (
                        root
                        / f"proofs/experiments/issue624/{language}/Schema.{extension}"
                    )
                    self.assertEqual(
                        path.read_text().split(generate_schema.MARKERS[language])[1],
                        f"\nProof tail for {language}.\n",
                    )


if __name__ == "__main__":
    unittest.main()
