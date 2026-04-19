#include "simulator/udp_eval.h"

#include "parser/ast.h"

namespace delta {

UdpEvalState::UdpEvalState(const UdpDecl& decl) : decl_(decl) {
  output_ =
      (decl_.is_sequential && decl_.has_initial) ? decl_.initial_value : 'x';
}

static bool IsEdgeSymbol(char symbol) {
  return symbol == 'r' || symbol == 'f' || symbol == 'p' || symbol == 'n' ||
         symbol == '*' || symbol == '\x01';
}

// §29.2: a z on a UDP input is observed as x for table matching and edge
// detection.
static char CoerceUdpInput(char value) { return value == 'z' ? 'x' : value; }

static std::vector<char> CoerceUdpInputs(const std::vector<char>& inputs) {
  std::vector<char> coerced;
  coerced.reserve(inputs.size());
  for (char v : inputs) coerced.push_back(CoerceUdpInput(v));
  return coerced;
}

static bool MatchLevel(char symbol, char value) {
  if (symbol == value) return true;
  if (symbol == '?') return value == '0' || value == '1' || value == 'x';
  if (symbol == 'b') return value == '0' || value == '1';
  return false;
}

static bool MatchEdge(char symbol, char prev, char curr) {
  if (symbol == 'r') return prev == '0' && curr == '1';
  if (symbol == 'f') return prev == '1' && curr == '0';
  if (symbol == '*') return prev != curr;
  if (symbol == 'p') {
    return (prev == '0' && curr == '1') || (prev == '0' && curr == 'x') ||
           (prev == 'x' && curr == '1');
  }
  if (symbol == 'n') {
    return (prev == '1' && curr == '0') || (prev == '1' && curr == 'x') ||
           (prev == 'x' && curr == '0');
  }
  return false;
}

void UdpEvalState::SetInputs(const std::vector<char>& inputs) {
  prev_inputs_ = CoerceUdpInputs(inputs);
}

// Check if all level symbols in a row match the given input values.
static bool MatchAllLevels(const UdpTableRow& row,
                           const std::vector<char>& inputs) {
  if (row.inputs.size() != inputs.size()) return false;
  for (size_t i = 0; i < inputs.size(); ++i) {
    if (!MatchLevel(row.inputs[i], inputs[i])) return false;
  }
  return true;
}

// Check if a row's current_state field matches the given output.
static bool MatchState(const UdpDecl& decl, const UdpTableRow& row,
                       char output) {
  if (!decl.is_sequential) return true;
  if (row.current_state == 0) return true;
  return MatchLevel(row.current_state, output);
}

// Resolve a row output: '-' means no change (keep current output).
static char ResolveOutput(char row_output, char current_output) {
  return (row_output == '-') ? current_output : row_output;
}

// §29.4: Combinational evaluation — pure level lookup.
char UdpEvalState::Evaluate(const std::vector<char>& inputs) {
  auto coerced = CoerceUdpInputs(inputs);
  for (const auto& row : decl_.table) {
    if (!MatchAllLevels(row, coerced)) continue;
    if (!MatchState(decl_, row, output_)) continue;
    output_ = ResolveOutput(row.output, output_);
    prev_inputs_ = coerced;
    return output_;
  }
  output_ = 'x';
  prev_inputs_ = coerced;
  return output_;
}

static bool MatchParenEdge(const UdpTableRow& row, size_t i, char prev_value,
                           char new_value) {
  if (i >= row.paren_edges.size()) return false;
  auto [from, to] = row.paren_edges[i];
  return MatchLevel(from, prev_value) && MatchLevel(to, new_value);
}

static bool MatchRowWithEdge(const UdpTableRow& row,
                             const std::vector<char>& new_inputs,
                             uint32_t changed_idx, char prev_value,
                             bool& has_edge) {
  if (row.inputs.size() != new_inputs.size()) return false;
  has_edge = false;
  for (size_t i = 0; i < new_inputs.size(); ++i) {
    char sym = row.inputs[i];
    if (!IsEdgeSymbol(sym)) {
      if (!MatchLevel(sym, new_inputs[i])) return false;
      continue;
    }
    has_edge = true;
    if (i != changed_idx) return false;
    if (sym == '\x01') {
      if (!MatchParenEdge(row, i, prev_value, new_inputs[i])) return false;
    } else if (!MatchEdge(sym, prev_value, new_inputs[i])) {
      return false;
    }
  }
  return true;
}

// §29.9/§29.10: Evaluate with edge detection and level-sensitive dominance.
char UdpEvalState::EvaluateWithEdge(const std::vector<char>& new_inputs,
                                    uint32_t changed_idx, char prev_value) {
  auto coerced_new = CoerceUdpInputs(new_inputs);
  char coerced_prev = CoerceUdpInput(prev_value);
  char edge_result = 0;
  char level_result = 0;

  for (const auto& row : decl_.table) {
    bool has_edge = false;
    if (!MatchRowWithEdge(row, coerced_new, changed_idx, coerced_prev,
                          has_edge))
      continue;
    if (!MatchState(decl_, row, output_)) continue;
    char result = ResolveOutput(row.output, output_);
    if (has_edge && edge_result == 0) edge_result = result;
    if (!has_edge && level_result == 0) level_result = result;
  }

  // §29.10: Level-sensitive dominates if both match.
  if (level_result != 0) {
    output_ = level_result;
  } else if (edge_result != 0) {
    output_ = edge_result;
  } else {
    output_ = 'x';
  }

  prev_inputs_ = coerced_new;
  return output_;
}

}  // namespace delta
