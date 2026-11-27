#include <algorithm>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_type_facts.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsFoldedVector(const DataType& type) {
  return (type.kind == DataTypeKind::kLogic ||
          type.kind == DataTypeKind::kBit) &&
         type.struct_members.empty() && type.enum_members.empty();
}

bool Elaborator::FoldMayDifferByPlace() const {
  return !active_loop_genvars_.empty() ||
         std::ranges::any_of(module_path_, [](const RtlirModule* outer) {
           return !outer->params.empty();
         });
}

const void* Elaborator::FoldedTypeRefOwner() const {
  if (!gen_body_owners_.empty()) return gen_body_owners_.back();
  return module_decl_path_.back();
}

void Elaborator::RecordFoldedTypeRef(std::string_view name,
                                     const DataType& type,
                                     const RtlirModule* mod) {
  typedefs_[name] = type;
  RecordPlaceTypeFacts(place_type_facts_[mod], name, InternedGenPrefix(),
                       {typedefs_, aggregate_typedef_names_, arena_});
}

bool Elaborator::AdoptFoldedTypeRef(DataType& dt, const Expr* ref,
                                    const std::optional<DataType>& type,
                                    const RtlirModule* mod) {
  if (!type || !IsFoldedVector(*type) || !FoldMayDifferByPlace()) return false;
  auto [named, fresh] = folded_type_ref_names_.try_emplace(ref);
  if (fresh) {
    named->second = *arena_.Create<std::string>(
        std::format("type({})", folded_type_ref_names_.size()));
  }
  folded_type_refs_[named->second] = {ref, FoldedTypeRefOwner(), *type};
  RecordFoldedTypeRef(named->second, *type, mod);
  DataType place_type;
  place_type.kind = DataTypeKind::kNamed;
  place_type.type_name = named->second;
  AdoptReferencedType(dt, place_type);
  return true;
}

void Elaborator::RefreshFoldedTypeRef(std::string_view name,
                                      const RtlirModule* mod) {
  auto found = folded_type_refs_.find(name);
  if (found == folded_type_refs_.end()) return;
  std::optional<DataType> type = TypeRefExprType(found->second.operand, mod);
  if (!type) return;
  found->second.folded = *type;
  RecordFoldedTypeRef(name, *type, mod);
}

void Elaborator::EnterFoldedTypeRefOwner(const void* owner) {
  for (const auto& [name, folded] : folded_type_refs_) {
    if (folded.owner == owner) typedefs_[name] = folded.folded;
  }
}

void Elaborator::LeaveFoldedTypeRefOwner(const void* owner,
                                         const RtlirModule* mod) {
  std::vector<std::string_view> owned;
  for (const auto& [name, folded] : folded_type_refs_) {
    if (folded.owner == owner) owned.push_back(name);
  }
  for (std::string_view name : owned) RefreshFoldedTypeRef(name, mod);
}

}  // namespace delta
