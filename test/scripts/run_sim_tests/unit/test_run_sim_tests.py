"""Unit tests for run_sim_tests module."""

import subprocess
from unittest.mock import MagicMock, patch

import run_sim_tests


class TestCollectTests:
    """Tests for the collect_tests() function."""

    def test_finds_sv_expected_pairs(self, sim_test_tree):
        """collect_tests() should return pairs of .sv and .expected files."""
        with patch.object(run_sim_tests, "TEST_DIR", sim_test_tree):
            pairs = run_sim_tests.collect_tests()
        names = [sv.stem for sv, _ in pairs]
        assert "hello" in names
        assert "fail" in names

    def test_ignores_sv_without_expected(self, sim_test_tree):
        """collect_tests() should skip .sv files that lack a .expected."""
        with patch.object(run_sim_tests, "TEST_DIR", sim_test_tree):
            pairs = run_sim_tests.collect_tests()
        names = [sv.stem for sv, _ in pairs]
        assert "orphan" not in names

    def test_returns_empty_list_when_no_pairs(self, tmp_path):
        """collect_tests() should return [] when no .sv/.expected pairs exist."""
        (tmp_path / "readme.txt").write_text("nothing here\n")
        with patch.object(run_sim_tests, "TEST_DIR", tmp_path):
            pairs = run_sim_tests.collect_tests()
        assert pairs == []


class TestRunTest:
    """Tests for the run_test() function."""

    def test_returns_true_on_matching_output(self, tmp_path):
        """run_test() should return (True, '') when stdout matches expected."""
        sv = tmp_path / "test.sv"
        sv.write_text("module test; endmodule\n")
        expected = tmp_path / "test.expected"
        expected.write_text("Hello, World!\n")

        mock_result = MagicMock()
        mock_result.stdout = "Hello, World!\n"
        with patch("run_sim_tests.subprocess.run", return_value=mock_result):
            ok, detail = run_sim_tests.run_test(sv, expected)
        assert ok is True
        assert detail == ""

    def test_returns_false_on_mismatched_output(self, tmp_path):
        """run_test() should return (False, diff) when stdout differs."""
        sv = tmp_path / "test.sv"
        sv.write_text("module test; endmodule\n")
        expected = tmp_path / "test.expected"
        expected.write_text("expected output\n")

        mock_result = MagicMock()
        mock_result.stdout = "wrong output\n"
        with patch("run_sim_tests.subprocess.run", return_value=mock_result):
            ok, detail = run_sim_tests.run_test(sv, expected)
        assert ok is False
        assert "expected output" in detail
        assert "wrong output" in detail

    def test_strips_trailing_newlines_before_comparing(self, tmp_path):
        """run_test() should strip trailing newlines from both sides."""
        sv = tmp_path / "test.sv"
        sv.write_text("module test; endmodule\n")
        expected = tmp_path / "test.expected"
        expected.write_text("output\n\n\n")

        mock_result = MagicMock()
        mock_result.stdout = "output\n"
        with patch("run_sim_tests.subprocess.run", return_value=mock_result):
            ok, detail = run_sim_tests.run_test(sv, expected)
        assert ok is True
        assert detail == ""

    def test_returns_timeout_on_timeout_expired(self, tmp_path):
        """run_test() should return (False, 'TIMEOUT') on TimeoutExpired."""
        sv = tmp_path / "test.sv"
        sv.write_text("module test; endmodule\n")
        expected = tmp_path / "test.expected"
        expected.write_text("output\n")

        with patch(
            "run_sim_tests.subprocess.run",
            side_effect=subprocess.TimeoutExpired(cmd="deltahdl", timeout=30),
        ):
            ok, detail = run_sim_tests.run_test(sv, expected)
        assert ok is False
        assert detail == "TIMEOUT"
