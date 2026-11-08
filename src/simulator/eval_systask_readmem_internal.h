#pragma once

#include <cstdint>
#include <cstdlib>
#include <string>

#include "common/arena.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "simulator/sim_context_types.h"

namespace delta {

struct Expr;
class SimContext;

struct ReadmemEnv {
  SimContext& ctx;
  Arena& arena;
  bool is_hex;
  SourceLoc loc;
};

struct ReadmemWindow {
  bool has_start;
  bool has_finish;
  int64_t start_arg;
  int64_t finish_arg;
};

bool DecodeMemNumberChar(char c, bool is_hex, uint8_t& aval, uint8_t& bval);
Logic4Vec ParseMemNumber(Arena& arena, const std::string& tok, bool is_hex,
                         uint32_t width);
void CoerceToTwoState(Logic4Vec& v);
bool EnumValueInRange(const EnumTypeInfo* info, const Logic4Vec& v);
bool IsMemFileSpace(char c);
bool SkipMemFileComment(const std::string& content, size_t n, size_t& pos);
std::string ScanMemFileToken(const std::string& content, size_t n, size_t& pos);
bool CheckMemFileToken(const ReadmemEnv& env, const std::string& tok);

void DoMemLoad(const ReadmemEnv& env, const std::string& content,
               const Expr* mn, const ReadmemWindow& w);

}  // namespace delta
