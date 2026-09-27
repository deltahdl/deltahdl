#include "parser/udp_row_overlap.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>

#include "parser/ast_specify.h"

namespace delta {
namespace {

// The levels a level_symbol admits, one bit each for 0, 1 and x.
constexpr uint8_t kLevel0 = 1;
constexpr uint8_t kLevel1 = 2;
constexpr uint8_t kLevelX = 4;

uint8_t LevelMask(char c) {
  switch (c) {
    case '0':
      return kLevel0;
    case '1':
      return kLevel1;
    case 'x':
    case 'X':
      return kLevelX;
    case 'b':
    case 'B':
      return kLevel0 | kLevel1;
    default:  // '?', and anything the row checks have already reported.
      return kLevel0 | kLevel1 | kLevelX;
  }
}

// The level a level bit stands for, 0, 1 or 2 for x.
int LevelIndex(uint8_t bit) {
  return bit == kLevel0 ? 0 : bit == kLevel1 ? 1 : 2;
}

// The transitions an edge admits, one bit per (from, to) pair of distinct
// levels, bit 3 * from + to.
uint16_t PairMask(uint8_t from, uint8_t to) {
  uint16_t mask = 0;
  for (uint8_t f = kLevel0; f <= kLevelX; f <<= 1) {
    for (uint8_t t = kLevel0; t <= kLevelX; t <<= 1) {
      if ((from & f) == 0 || (to & t) == 0 || f == t) continue;
      mask |= static_cast<uint16_t>(1U << (3 * LevelIndex(f) + LevelIndex(t)));
    }
  }
  return mask;
}

// Table 29-1's edge symbols: r (01), f (10), p (01), (0x), (x1), n (10), (1x),
// (x0), and * any change.
uint16_t EdgeSymbolMask(char c) {
  switch (c) {
    case 'r':
    case 'R':
      return PairMask(kLevel0, kLevel1);
    case 'f':
    case 'F':
      return PairMask(kLevel1, kLevel0);
    case 'p':
    case 'P':
      return PairMask(kLevel0, kLevel1) | PairMask(kLevel0, kLevelX) |
             PairMask(kLevelX, kLevel1);
    case 'n':
    case 'N':
      return PairMask(kLevel1, kLevel0) | PairMask(kLevel1, kLevelX) |
             PairMask(kLevelX, kLevel0);
    default:  // '*'
      return PairMask(kLevel0 | kLevel1 | kLevelX, kLevel0 | kLevel1 | kLevelX);
  }
}

bool IsEdgeField(char c) {
  switch (c) {
    case '\x01':
    case 'r':
    case 'R':
    case 'f':
    case 'F':
    case 'p':
    case 'P':
    case 'n':
    case 'N':
    case '*':
      return true;
    default:
      return false;
  }
}

// The input a row's transition is on, if it has one.
std::optional<std::size_t> EdgeInput(const UdpTableRow& row) {
  for (std::size_t i = 0; i < row.inputs.size(); ++i) {
    if (IsEdgeField(row.inputs[i])) return i;
  }
  return std::nullopt;
}

uint16_t EdgeMaskAt(const UdpTableRow& row, std::size_t i) {
  if (row.inputs[i] != '\x01') return EdgeSymbolMask(row.inputs[i]);
  const std::pair<char, char> kEdge =
      i < row.paren_edges.size() ? row.paren_edges[i] : std::pair<char, char>{};
  return PairMask(LevelMask(kEdge.first), LevelMask(kEdge.second));
}

// Whether the two rows' input fields admit a common combination.
bool InputsOverlap(const UdpTableRow& a, const UdpTableRow& b) {
  if (a.inputs.size() != b.inputs.size()) return false;
  const std::optional<std::size_t> kEdgeA = EdgeInput(a);
  const std::optional<std::size_t> kEdgeB = EdgeInput(b);
  if (kEdgeA != kEdgeB) return false;
  for (std::size_t i = 0; i < a.inputs.size(); ++i) {
    if (kEdgeA == i) {
      if ((EdgeMaskAt(a, i) & EdgeMaskAt(b, i)) == 0) return false;
    } else if ((LevelMask(a.inputs[i]) & LevelMask(b.inputs[i])) == 0) {
      return false;
    }
  }
  return true;
}

// The output a row gives in state `state` (a level bit): its output symbol, or
// the state itself where the symbol is `-`.
uint8_t OutputIn(const UdpTableRow& row, uint8_t state) {
  return row.output == '-' ? state : LevelMask(row.output);
}

}  // namespace

bool UdpRowsConflict(const UdpTableRow& a, const UdpTableRow& b) {
  if (!InputsOverlap(a, b)) return false;
  // A combinational row has no current-state field and stands in every state.
  const uint8_t kStatesA = a.current_state == 0 ? kLevel0 | kLevel1 | kLevelX
                                                : LevelMask(a.current_state);
  const uint8_t kStatesB = b.current_state == 0 ? kLevel0 | kLevel1 | kLevelX
                                                : LevelMask(b.current_state);
  for (uint8_t state = kLevel0; state <= kLevelX; state <<= 1) {
    if ((kStatesA & kStatesB & state) == 0) continue;
    if (OutputIn(a, state) != OutputIn(b, state)) return true;
  }
  return false;
}

}  // namespace delta
