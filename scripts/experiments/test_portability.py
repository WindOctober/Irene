import asyncio
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import run
from portable import portable_text


class PortabilityTests(unittest.TestCase):
    def test_archive_does_not_require_git(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(run, "ROOT", Path(directory)), patch.object(
                run.subprocess, "check_output", side_effect=AssertionError("Git must not run")
            ):
                self.assertEqual(set(run.commits().values()), {"source-archive"})

    def test_real_checkout_and_empty_git_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            with patch.object(run, "ROOT", root):
                self.assertEqual(run.commits()["irene"], "source-archive")
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Test",
                            "-c", "user.email=test@localhost", "commit", "-q",
                            "--allow-empty", "-m", "test"], check=True)
            with patch.object(run, "ROOT", root):
                self.assertNotEqual(run.commits()["irene"], "source-archive")

    def test_saved_job_remains_executable_from_root(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "input.qasm").write_text("OPENQASM 2.0;")
            job = root / "jobs/case.json"
            with patch.object(run, "ROOT", root):
                run.atomic_write(job, json.dumps({"left_abs": str(root / "input.qasm")}))
                self.assertEqual(json.loads(job.read_text())["left_abs"], "./input.qasm")
                code = ("import json,pathlib; j=json.load(open('jobs/case.json')); "
                        "assert pathlib.Path(j['left_abs']).read_text()=='OPENQASM 2.0;'")
                result = asyncio.run(run.run_process(
                    [sys.executable, "-c", code], 10, 1024**3, None))
                self.assertEqual(result[0], 0, result[-1])

    def test_metadata_keys_and_external_interpreter(self):
        with tempfile.TemporaryDirectory() as directory:
            text = json.dumps({directory + "/input": [sys.executable, directory + "/trace"]})
            value = json.loads(portable_text(text, directory))
            self.assertEqual(value["./input"], [Path(sys.executable).name, "./trace"])
            self.assertNotIn(directory, json.dumps(value))


if __name__ == "__main__":
    unittest.main()
