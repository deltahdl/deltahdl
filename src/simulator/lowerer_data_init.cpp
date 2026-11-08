#include <algorithm>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/unit_scope_items.h"

namespace delta {

static void RegisterDesignTypeWidths(const RtlirDesign* design,
                                     SimContext& ctx) {
  for (const auto& [name, width] : design->type_widths) {
    ctx.RegisterTypeWidth(name, width);
  }
  for (const auto& [name, kind] : design->type_kinds) {
    ctx.RegisterTypeKind(name, kind);
  }
  for (const auto& [name, is_signed] : design->type_signed) {
    ctx.RegisterTypeSigned(name, is_signed);
  }
  for (const auto& [name, range] : design->type_ranges) {
    ctx.RegisterTypeRange(name, range);
  }
}

static void RegisterUnitTypeRefCompares(const RtlirDesign* design,
                                        SimContext& ctx) {
  for (const TypeRefCompareResult& compare : design->unit_type_ref_compares) {
    ctx.RecordUnitTypeRefCompare(compare.expr, compare.holds);
  }
}

void Lowerer::LowerDesignData() {
  RegisterUnitTypeRefCompares(design_, ctx_);
  RegisterDesignTypeWidths(design_, ctx_);
  RegisterTypeTargets(design_, ctx_);
  RegisterDesignTypeLayouts(design_, ctx_, arena_);
  RegisterDesignEnumTypes(design_, ctx_, arena_);
  RegisterUnitClassVariables(design_, ctx_, arena_);
  RegisterPackageScopedSubroutines(design_, ctx_, arena_);
  RegisterPackageEnumConstants(design_, ctx_, arena_);
  CreatePackageDataVariables(design_, ctx_, arena_);
  CreateUnitDataVariables(design_, ctx_, arena_);
  CreateUnitNets(design_, ctx_, arena_);
  AliasPackageExports(design_, ctx_, arena_);
  InitPackageDataVariables(design_, ctx_, arena_);
}

void Lowerer::InitCompilationUnitData() {
  LowerCompilationUnitImports();
  InitUnitDataVariables(design_, ctx_, arena_);
}

void Lowerer::ConstructDesignData() {
  LowerUnimportedPackageClasses();
  ConstructDataClassInitializers(design_, ctx_, arena_);
}

static std::vector<std::string_view> UnboundPackageClassNames(
    const RtlirDesign* design, SimContext& ctx) {
  std::vector<std::string_view> names;
  for (const auto* pkg : design->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl)
        continue;
      std::string_view name = item->class_decl->name;
      bool seen = std::find(names.begin(), names.end(), name) != names.end();
      if (!seen && ctx.FindClassType(name) == nullptr) names.push_back(name);
    }
  }
  return names;
}

void Lowerer::LowerUnitClassPackageBases() {
  const std::vector<const ClassDecl*> kUnitClasses =
      UnitClassesToLower(design_);
  for (const auto* pkg : design_->packages) {
    const bool kNamed =
        std::ranges::any_of(kUnitClasses, [pkg](const ClassDecl* cls) {
          return cls->base_class_scope == pkg->name;
        });
    if (!kNamed) continue;
    std::vector<std::pair<std::string_view, ClassTypeInfo*>> held;
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kClassDecl) continue;
      held.emplace_back(item->class_decl->name,
                        ctx_.FindClassType(item->class_decl->name));
    }
    LowerUnimportedClassesOf(pkg);
    for (const auto& [name, info] : held) ctx_.RegisterClassType(name, info);
  }
}

void Lowerer::LowerUnimportedPackageClasses() {
  if (!design_) return;
  std::vector<std::string_view> unbound =
      UnboundPackageClassNames(design_, ctx_);
  for (const auto* pkg : design_->packages) LowerUnimportedClassesOf(pkg);
  RegisterClassTypeAliases(design_, ctx_, arena_);
  for (std::string_view name : unbound) ctx_.RegisterClassType(name, nullptr);
}

}  // namespace delta
