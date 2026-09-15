from typing import Any


_Records = dict[str, dict[str, Any]]


def _adjacency(records: _Records) -> dict[str, list[str]]:
    keys = set(records)
    return {
        sub: [d for d in records[sub]["dependencies"] if d in keys]
        for sub in records
    }


def find_cycle_groups(records: _Records) -> list[list[str]]:
    adj = _adjacency(records)
    index_counter = [0]
    stack: list[str] = []
    on_stack: dict[str, bool] = {}
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    components: list[list[str]] = []

    def _strongconnect(node: str) -> None:
        indices[node] = index_counter[0]
        lowlinks[node] = index_counter[0]
        index_counter[0] += 1
        stack.append(node)
        on_stack[node] = True
        for successor in adj[node]:
            if successor not in indices:
                _strongconnect(successor)
                lowlinks[node] = min(lowlinks[node], lowlinks[successor])
            elif on_stack.get(successor):
                lowlinks[node] = min(lowlinks[node], indices[successor])
        if lowlinks[node] == indices[node]:
            component: list[str] = []
            while True:
                top = stack.pop()
                on_stack[top] = False
                component.append(top)
                if top == node:
                    break
            components.append(component)

    for node in adj:
        if node not in indices:
            _strongconnect(node)
    return components


def order_groups(
    groups: list[list[str]], records: _Records,
) -> list[list[str]]:
    adj = _adjacency(records)
    member_to_group: dict[str, int] = {
        member: idx for idx, group in enumerate(groups) for member in group
    }
    successors: dict[int, set[int]] = {idx: set() for idx in range(len(groups))}
    for idx, group in enumerate(groups):
        for member in group:
            for dep in adj.get(member, []):
                target = member_to_group.get(dep)
                if target is not None and target != idx:
                    successors[idx].add(target)

    visited: set[int] = set()
    order: list[int] = []

    def _visit(node: int) -> None:
        if node in visited:
            return
        visited.add(node)
        for nxt in sorted(successors[node]):
            _visit(nxt)
        order.append(node)

    for idx in range(len(groups)):
        _visit(idx)
    return [groups[idx] for idx in order]
