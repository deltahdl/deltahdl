#include "simulator/vpi_table_entry_value.h"

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The symbols of `row`, each one or two characters: a field written in
// parentheses is an edge, the two levels it names; any other character but a
// space or a field separator is a symbol of its own.
std::vector<std::string_view> RowSymbols(std::string_view row) {
  std::vector<std::string_view> symbols;
  for (std::size_t i = 0; i < row.size(); ++i) {
    const char kChar = row[i];
    if (kChar == ' ' || kChar == ':') continue;
    if (kChar == '(' && i + 3 < row.size() && row[i + 3] == ')') {
      symbols.push_back(row.substr(i + 1, 2));
      i += 3;
      continue;
    }
    symbols.push_back(row.substr(i, 1));
  }
  return symbols;
}

}  // namespace

std::vector<s_vpi_vecval> VpiTableEntryVector(std::string_view row) {
  const std::vector<std::string_view> kSymbols = RowSymbols(row);
  std::vector<s_vpi_vecval> vector(
      kSymbols.empty() ? 1 : (kSymbols.size() - 1) / 4 + 1, s_vpi_vecval{0, 0});
  for (std::size_t k = 0; k < kSymbols.size(); ++k) {
    const std::string_view kSymbol = kSymbols[k];
    uint32_t pair =
        static_cast<uint32_t>(static_cast<unsigned char>(kSymbol[0])) << 8;
    if (kSymbol.size() > 1) pair |= static_cast<unsigned char>(kSymbol[1]);
    const uint32_t kShift = (k % 2 == 0) ? 16 : 0;
    s_vpi_vecval& element = vector[k / 4];
    PLI_UINT32& half = (k % 4 < 2) ? element.aval : element.bval;
    half |= pair << kShift;
  }
  return vector;
}

}  // namespace delta
