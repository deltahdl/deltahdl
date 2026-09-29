#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>

#include "elaborator/rtlir_scopes.h"

namespace delta {

struct RtlirModule;

// §27.4: the generate block instance one item is elaborated in. `path` names
// the instance (§23.6), `prefix` is the prefix its declarations are stored
// under, and `prefixes` are the prefixes of the instance and of every block
// around it, outermost first, as GenBlockPrefixes holds them.
struct GenBlockInstanceScope {
  const HierPath& path;
  std::string_view prefix;
  const GenBlockPrefixes& prefixes;
};

// §27.4 and §27.5 with §23.6: how far `mod`'s variables, nets, parameters and
// clocking blocks reached before one item of a generate block instance was
// elaborated, so what the item declared is what lies past it.
struct DeclarationCounts {
  size_t variables = 0;
  size_t nets = 0;
  size_t params = 0;
  size_t clocking_blocks = 0;
};

DeclarationCounts CountDeclarations(const RtlirModule* mod);

// Lists what one item of the generate block instance `scope` declared, past
// `before`, as members of that instance (RtlirGenBlockMember), and each
// clocking block it declared with the instance's path and prefixes
// (RtlirGenBlockClocking).
void RecordBlockItemMembers(RtlirModule* mod,
                            const GenBlockInstanceScope& scope,
                            const DeclarationCounts& before);

// Retargets the loop block step ending `path` at the instance `index` and
// records its implicit localparam `genvar_name` (§27.4).
void EnterLoopBlockInstance(RtlirModule* mod, HierPath& path,
                            std::string_view genvar_name, int64_t index);

}  // namespace delta
