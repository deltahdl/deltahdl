#include "simulation/net.h"

#include "common/arena.h"
#include "simulation/variable.h"

namespace delta {

// --- Per-word resolution helpers ---

Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b) {
  // IEEE §28.7 wire/tri resolution table:
  //   z resolves to the other driver; conflicting known bits produce x.
  uint64_t a_z = a.aval & a.bval;
  uint64_t b_z = b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_x = ~a.aval & a.bval;
  uint64_t b_x = ~b.aval & b.bval;
  uint64_t conflict = ~a.bval & ~b.bval & (a.aval ^ b.aval);
  uint64_t unknown = (a_x | b_x | conflict) & neither_z;

  uint64_t res_aval = both_z | (b.aval & a_only_z) | (a.aval & b_only_z) |
                      (a.aval & neither_z & ~unknown);
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | unknown;
  return {res_aval, res_bval};
}

Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b) {
  // Wand/triand: AND semantics. 0 dominates, z defers to other driver.
  uint64_t a_z = a.aval & a.bval;
  uint64_t b_z = b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_0 = ~a.aval & ~a.bval;
  uint64_t b_0 = ~b.aval & ~b.bval;
  uint64_t either_0 = (a_0 | b_0) & neither_z;
  uint64_t a_x = ~a.aval & a.bval;
  uint64_t b_x = ~b.aval & b.bval;
  uint64_t either_x = (a_x | b_x) & neither_z & ~either_0;
  uint64_t both_1 = a.aval & ~a.bval & b.aval & ~b.bval & neither_z;

  uint64_t res_aval =
      both_z | (b.aval & a_only_z) | (a.aval & b_only_z) | both_1;
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | either_x;
  return {res_aval, res_bval};
}

Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b) {
  // Wor/trior: OR semantics. 1 dominates, z defers to other driver.
  uint64_t a_z = a.aval & a.bval;
  uint64_t b_z = b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_1 = a.aval & ~a.bval;
  uint64_t b_1 = b.aval & ~b.bval;
  uint64_t either_1 = (a_1 | b_1) & neither_z;
  uint64_t a_x = ~a.aval & a.bval;
  uint64_t b_x = ~b.aval & b.bval;
  uint64_t either_x = (a_x | b_x) & neither_z & ~either_1;

  uint64_t res_aval =
      both_z | (b.aval & a_only_z) | (a.aval & b_only_z) | either_1;
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | either_x;
  return {res_aval, res_bval};
}

// --- Net::Resolve ---

void Net::Resolve(Arena& arena) {
  if (!resolved || drivers.empty()) return;
  if (drivers.size() == 1) {
    resolved->value = drivers[0];
    resolved->NotifyWatchers();
    return;
  }

  // Fold drivers pairwise using the appropriate resolution function.
  Logic4Vec result = drivers[0];
  for (size_t i = 1; i < drivers.size(); ++i) {
    auto combined = MakeLogic4Vec(arena, result.width);
    for (uint32_t w = 0; w < result.nwords; ++w) {
      switch (type) {
        case NetType::kWire:
        case NetType::kTri:
          combined.words[w] =
              ResolveWireWord(result.words[w], drivers[i].words[w]);
          break;
        case NetType::kWand:
        case NetType::kTriand:
          combined.words[w] =
              ResolveWandWord(result.words[w], drivers[i].words[w]);
          break;
        case NetType::kWor:
        case NetType::kTrior:
          combined.words[w] =
              ResolveWorWord(result.words[w], drivers[i].words[w]);
          break;
        default:
          combined.words[w] =
              ResolveWireWord(result.words[w], drivers[i].words[w]);
          break;
      }
    }
    result = combined;
  }
  resolved->value = result;
  resolved->NotifyWatchers();
}

}  // namespace delta
