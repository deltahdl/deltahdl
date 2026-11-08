#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

class SimContext;
struct Expr;

struct AssignNames {
  const std::unordered_map<std::string_view, VpiObject*>& objects;
  const std::string& prefix;
  const GenBlockPrefixes& gen;
  const VpiObject* scope = nullptr;
  const GenBlockConsts& genvars = NoGenvars();
  const VpiObject* instance = nullptr;
  const std::vector<RtlirImport>& imports = NoImports();
  int unit = -1;
  const VpiObjectMap& unit_typespecs = VpiAttachBuild::NoTypespecs();

  static const GenBlockConsts& NoGenvars() {
    static const GenBlockConsts kNone;
    return kNone;
  }
  static const std::vector<RtlirImport>& NoImports() {
    static const std::vector<RtlirImport> kNone;
    return kNone;
  }
};

inline const VpiObject* InnermostScope(const AssignNames& names) {
  return names.scope != nullptr ? names.scope : names.instance;
}

VpiHandle Resolve(const AssignNames& names, std::string_view name);

struct AssignBuild {
  std::function<VpiObject*()> alloc;
  SimContext* sim;
  AssignNames names;
  VpiCalleeResolver callees;
  std::function<std::string_view(std::string)> keep;
  std::function<bool(const Expr&, VpiObject*)> shape_call = nullptr;
  const RtlirNodeAttributes* attrs = nullptr;
};

void CollectReads(const Expr* expr, std::vector<std::string_view>& out);

std::optional<int64_t> ElaborationConstant(const Expr* expr,
                                           const AssignBuild& build);

Logic4Vec ValueWhereWritten(const Expr* expr, const AssignBuild& build);

int64_t ConstantWhereWritten(const Expr* constant, const AssignBuild& build);

VpiObject* ExpressionObject(const Expr* expr, const AssignBuild& build);

VpiObject* VpiTypedCast(VpiObject* op, const Expr& cast,
                        const AssignBuild& build);

void VpiSizeExpression(VpiObject* obj, const Expr& expr,
                       const AssignBuild& build);

VpiObject* AssignedExpressionObject(const Expr* expr, const VpiObject* target,
                                    const AssignBuild& build);

}  // namespace delta
