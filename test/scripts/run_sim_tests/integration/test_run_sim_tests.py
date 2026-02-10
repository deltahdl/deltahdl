"""Integration tests for run_sim_tests module."""

from unittest.mock import MagicMock, patch

import pytest

import run_sim_tests


class TestCollectAndRunPipeline:
    """Tests for the collect_tests() -> run_test() pipeline."""

    def test_all_pass_scenario(self, sim_test_tree):
        """All tests passing should yield correct pass/fail counts."""
        with patch.object(run_sim_tests, "TEST_DIR", sim_test_tree):
            pairs = run_sim_tests.collect_tests()

        results = []
        for sv, expected_path in pairs:
            expected_text = expected_path.read_text().rstrip("\n")
            mock_result = MagicMock()
            mock_result.stdout = expected_text + "\n"
            with patch(
                "run_sim_tests.subprocess.run", return_value=mock_result
            ):
                ok, detail = run_sim_tests.run_test(sv, expected_path)
            results.append(ok)

        assert all(results)
        assert len(results) == 2  # hello + fail (orphan excluded)

    def test_mixed_pass_fail_scenario(self, sim_test_tree):
        """Mixed results should report correct counts."""
        with patch.object(run_sim_tests, "TEST_DIR", sim_test_tree):
            pairs = run_sim_tests.collect_tests()

        pass_count = 0
        fail_count = 0
        for sv, expected_path in pairs:
            mock_result = MagicMock()
            if sv.stem == "hello":
                mock_result.stdout = "Hello, World!\n"
            else:
                mock_result.stdout = "wrong output\n"
            with patch(
                "run_sim_tests.subprocess.run", return_value=mock_result
            ):
                ok, _ = run_sim_tests.run_test(sv, expected_path)
            pass_count += ok
            fail_count += not ok

        assert pass_count == 1
        assert fail_count == 1


class TestMain:
    """Tests for the main() function."""

    def test_all_passing_exits_zero(self, sim_test_tree):
        """main() should call sys.exit(0) when all tests pass."""
        mock_result = MagicMock()

        def fake_run(cmd, **kwargs):
            sv_path = cmd[1]
            expected_path = sv_path.replace(".sv", ".expected")
            with open(expected_path) as f:
                mock = MagicMock()
                mock.stdout = f.read()
            return mock

        with patch.object(run_sim_tests, "TEST_DIR", sim_test_tree), \
             patch("run_sim_tests.check_binary"), \
             patch("run_sim_tests.subprocess.run", side_effect=fake_run), \
             pytest.raises(SystemExit) as exc_info:
            run_sim_tests.main()

        assert exc_info.value.code == 0
