"""Generate DOT Graphviz output from the figure data model."""

from convert_figures._models import Edge, Figure, Node


def format_node(node: Node) -> str:
    """Format a single node as a DOT statement."""
    escaped = node.label.replace('"', '\\"')
    return f'  {node.node_id} [label="{escaped}"];'


def format_edge(edge: Edge) -> str:
    """Format a single edge as a DOT statement."""
    return f"  {edge.source} -> {edge.target};"


def figure_number_to_graph_name(number: str) -> str:
    """Convert a figure number like '4-1' to a graph name like 'Figure_4_1'."""
    return "Figure_" + number.replace("-", "_")


def generate_dot(figure: Figure) -> str:
    """Generate complete DOT digraph source for a figure."""
    lines: list[str] = []
    lines.append(f"digraph {figure.graph_name} {{")
    lines.append("  rankdir=TB;")
    if figure.nodes:
        lines.append("")
        for node in figure.nodes:
            lines.append(format_node(node))
    if figure.edges:
        lines.append("")
        for edge in figure.edges:
            lines.append(format_edge(edge))
    lines.append("}")
    return "\n".join(lines) + "\n"
