"""Data model for figure-to-DOT conversion."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Node:
    """A graph node representing a labeled box in a figure."""

    node_id: str
    label: str


@dataclass(frozen=True)
class Edge:
    """A directed edge between two nodes."""

    source: str
    target: str


@dataclass(frozen=True)
class Figure:
    """A complete figure extracted from the LRM."""

    number: str
    title: str
    graph_name: str
    nodes: tuple[Node, ...]
    edges: tuple[Edge, ...]


def label_to_node_id(label: str) -> str:
    """Convert a figure label to a DOT node identifier.

    Removes hyphens and replaces spaces with underscores.
    """
    return label.replace("-", "").replace(" ", "_")
