#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>

#include "elaborator/rtlir_scopes.h"

namespace delta {

struct RtlirModule;

struct GenBlockInstanceScope {
  const HierPath& path;
  std::string_view prefix;
  const GenBlockPrefixes& prefixes;
};

struct DeclarationCounts {
  size_t variables = 0;
  size_t nets = 0;
  size_t params = 0;
  size_t clocking_blocks = 0;
};

DeclarationCounts CountDeclarations(const RtlirModule* mod);

void RecordBlockItemMembers(RtlirModule* mod,
                            const GenBlockInstanceScope& scope,
                            const DeclarationCounts& before);

void EnterLoopBlockInstance(RtlirModule* mod, HierPath& path,
                            std::string_view genvar_name, int64_t index);

}  // namespace delta
