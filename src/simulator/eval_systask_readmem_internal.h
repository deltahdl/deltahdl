#pragma once

#include <cstdint>
#include <cstdlib>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/sim_context_types.h"

namespace delta {

// §21.4: the lexical layer of a $readmemb / $readmemh load file -- the number
// grammar the task name's radix fixes, and the white space and comment forms
// that separate one number from the next.

bool DecodeMemNumberChar(char c, bool is_hex, uint8_t& aval, uint8_t& bval);
Logic4Vec ParseMemNumber(Arena& arena, const std::string& tok, bool is_hex,
                         uint32_t width);
void CoerceToTwoState(Logic4Vec& v);
bool EnumValueInRange(const EnumTypeInfo* info, const Logic4Vec& v);
bool IsMemFileSpace(char c);
bool SkipMemFileComment(const std::string& content, size_t n, size_t& pos);
std::string ScanMemFileToken(const std::string& content, size_t n, size_t& pos);

}  // namespace delta
