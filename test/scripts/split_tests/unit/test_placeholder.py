"""Placeholder so the unit-test job has at least one test to collect."""

import split_tests


def test_tee_writer_write(capsys):
    """TeeWriter.write sends data to all streams."""
    import sys
    writer = split_tests.TeeWriter(sys.__stdout__)
    writer.write("hello")
    captured = capsys.readouterr()
    assert captured.out == "hello"
