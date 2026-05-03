"""Unit tests for cycle finding and dependency-respecting group ordering."""

from document_dependency_graph.ordering import find_cycle_groups, order_groups


def _records(graph):
    """Wrap a {sub: [deps]} dict into the per-subclause record shape."""
    return {
        sub: {"dependencies": deps, "proofs": {}, "prerequisites": {}}
        for sub, deps in graph.items()
    }


def test_single_subclause_no_deps_is_one_group() -> None:
    """A subclause with no dependencies is its own one-element group."""
    groups = find_cycle_groups(_records({"4.4": []}))
    assert groups == [["4.4"]]


def test_two_subclause_cycle_shares_one_group() -> None:
    """A↔B mutual dependency yields one group containing both."""
    groups = find_cycle_groups(_records({"A": ["B"], "B": ["A"]}))
    assert [sorted(g) for g in groups] == [["A", "B"]]


def test_transitive_cycle_collapses_to_one_group() -> None:
    """A→B→C→A all collapse into one group; isolated D stays separate."""
    graph = {"A": ["B"], "B": ["C"], "C": ["A"], "D": []}
    groups = find_cycle_groups(_records(graph))
    sorted_groups = sorted(sorted(g) for g in groups)
    assert sorted_groups == [["A", "B", "C"], ["D"]]


def test_diamond_dag_keeps_groups_separate() -> None:
    """A→B, A→C, B→C: every subclause is its own group (no cycles)."""
    graph = {"A": ["B", "C"], "B": ["C"], "C": []}
    groups = find_cycle_groups(_records(graph))
    sorted_groups = sorted(sorted(g) for g in groups)
    assert sorted_groups == [["A"], ["B"], ["C"]]


# --- order_groups ----------------------------------------------------------


def test_order_groups_places_dependency_first() -> None:
    """A depends on B → [B] is ordered before [A] (foundations first)."""
    records = _records({"A": ["B"], "B": []})
    ordered = order_groups([["A"], ["B"]], records)
    assert ordered == [["B"], ["A"]]


def test_order_groups_keeps_independent_groups() -> None:
    """Groups with no inter-group edge each appear once."""
    records = _records({"A": [], "B": []})
    ordered = order_groups([["A"], ["B"]], records)
    assert sorted(g[0] for g in ordered) == ["A", "B"]


def test_order_groups_orders_around_cycle_group() -> None:
    """A cycle group is placed after groups it depends on."""
    records = _records({"A": ["B"], "B": ["A"], "C": ["A"], "D": []})
    ordered = order_groups([["A", "B"], ["C"], ["D"]], records)
    cycle_pos = next(i for i, g in enumerate(ordered) if "A" in g)
    c_pos = next(i for i, g in enumerate(ordered) if g == ["C"])
    assert cycle_pos < c_pos
