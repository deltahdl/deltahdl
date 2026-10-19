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

// Where the class declaring a method is declared: in the design `design`, by
// the module `mod`, or by the package named `package` where no module
// declares it, or by the compilation unit where neither does; `params` is the
// instance prefix a width the method writes reads its parameters under.
struct VpiMethodScope {
  const RtlirDesign& design;
  const RtlirModule* mod;
  std::string_view package;
  std::string params;
};

// §37.41 details 1 to 3 and 12 with the figure: gives the method `method`
// made for the declaration `item` what every task and function holds: an io
// decl per argument, the variable a function returns through with the
// function's size, sign, function type and return range, and the variables
// its body declares, the body an out-of-block declaration writes for an
// extern method (§8.24). A type it names resolves where `where` says, and a
// width is read in the run `ctx`.
void VpiMakeMethodContents(VpiObject* method, const ModuleItem& item,
                           const VpiMethodScope& where, SimContext& ctx,
                           const VpiAttachBuild& build);

}  // namespace delta
