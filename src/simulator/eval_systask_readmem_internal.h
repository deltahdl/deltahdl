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

// §21.4: the invariant environment of one $readmem / $sreadmem invocation: the
// simulation context, the arena that owns parsed words, and the radix selected
// by the task name (hexadecimal for the *h forms, binary for the *b forms),
// together with where the call was written. Carried as one unit because every
// step of a load needs all four. A load reports against the file contents and
// the destination array rather than against an expression, so the call is the
// position every one of its reports names.
struct ReadmemEnv {
  SimContext& ctx;
  Arena& arena;
  bool is_hex;
  SourceLoc loc;
};

// §21.4: the optional start_addr / finish_addr task arguments. They fix the
// initial load cursor, the load direction, and (with no @-address in the file)
// the expected word count. `has_start` / `has_finish` record which were given;
// $sreadmem (§D.14) always supplies both.
struct ReadmemWindow {
  bool has_start;
  bool has_finish;
  int64_t start_arg;
  int64_t finish_arg;
};

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

// §21.4 / §D.14: loads `content`, text in the §21.4 load-file grammar, into
// the memory `mn` names -- a bare unpacked array, a partially indexed
// multidimensional one, a lowest-dimension slice of one, a dynamic array,
// queue or associative array, or a class object's array property -- within
// the address window `w`. $readmem and $sreadmem share it.
void DoMemLoad(const ReadmemEnv& env, const std::string& content,
               const Expr* mn, const ReadmemWindow& w);

}  // namespace delta
