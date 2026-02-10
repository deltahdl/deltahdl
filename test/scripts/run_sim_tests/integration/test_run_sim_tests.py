"""Integration tests for run_sim_tests module."""

from unittest.mock import MagicMock, patch

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
                ok, _ = run_sim_tests.run_test(sv, expected_path)
            results.append(ok)

        assert all(results) and len(results) == 2

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

        assert (pass_count, fail_count) == (1, 1)


class TestMain:
    """Tests for the main() function."""

    def test_all_passing_exits_zero(self, sim_test_tree, get_exit_code):
        """main() should call sys.exit(0) when all tests pass."""

        def fake_run(cmd, **_):
            sv_path = cmd[1]
            expected_path = sv_path.replace(".sv", ".expected")
            with open(expected_path, encoding="utf-8") as f:
                mock = MagicMock()
                mock.stdout = f.read()
            return mock

        def run():
            with patch.object(run_sim_tests, "TEST_DIR", sim_test_tree), \
                 patch("run_sim_tests.check_binary"), \
                 patch("run_sim_tests.subprocess.run", side_effect=fake_run):
                run_sim_tests.main()

        assert get_exit_code(run) == 0

    def test_no_pairs_exits_one(self, tmp_path, get_exit_code):
        """main() should exit 1 when no .sv/.expected pairs exist."""

        def run():
            with patch.object(run_sim_tests, "TEST_DIR", tmp_path), \
                 patch("run_sim_tests.check_binary"):
                run_sim_tests.main()

        assert get_exit_code(run) == 1

    def test_prints_detail_on_failure(self, sim_test_tree, capsys, get_exit_code):
        """main() should print indented detail lines when a test fails."""

        def fake_run(_cmd, **_):
            mock = MagicMock()
            mock.stdout = "wrong output\n"
            return mock

        def run():
            with patch.object(run_sim_tests, "TEST_DIR", sim_test_tree), \
                 patch("run_sim_tests.check_binary"), \
                 patch("run_sim_tests.subprocess.run", side_effect=fake_run):
                run_sim_tests.main()

        get_exit_code(run)
        assert "    expected:" in capsys.readouterr().out
