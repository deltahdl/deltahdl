#pragma once

#include <string>
#include <string_view>

namespace delta {

struct ModuleItem;
struct RtlirDesign;
struct RtlirModule;
class SimContext;
struct VpiAttachBuild;
struct VpiObject;

struct VpiMethodScope {
  const RtlirDesign& design;
  const RtlirModule* mod;
  std::string_view package;
  std::string params;
};

void VpiMakeMethodContents(VpiObject* method, const ModuleItem& item,
                           const VpiMethodScope& where, SimContext& ctx,
                           const VpiAttachBuild& build);

}  // namespace delta
