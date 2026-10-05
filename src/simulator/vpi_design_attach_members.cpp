#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

int VpiDataTypeVariableKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
      return vpiByteVar;
    case DataTypeKind::kShortint:
      return vpiShortIntVar;
    case DataTypeKind::kInt:
      return vpiIntVar;
    case DataTypeKind::kLongint:
      return vpiLongIntVar;
    case DataTypeKind::kInteger:
      return vpiIntegerVar;
    case DataTypeKind::kTime:
      return vpiTimeVar;
    case DataTypeKind::kBit:
      return vpiBitVar;
    case DataTypeKind::kStruct:
      return vpiStructVar;
    case DataTypeKind::kUnion:
      return vpiUnionVar;
    // §6.12 makes realtime a synonym for real.
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return vpiRealVar;
    case DataTypeKind::kShortreal:
      return vpiShortRealVar;
    case DataTypeKind::kString:
      return vpiStringVar;
    case DataTypeKind::kChandle:
      return vpiChandleVar;
    case DataTypeKind::kEnum:
      return vpiEnumVar;
    // §37.27 and §37.29.
    case DataTypeKind::kEvent:
      return vpiNamedEvent;
    case DataTypeKind::kVirtualInterface:
      return vpiVirtualInterfaceVar;
    default:
      return kVpiReg;
  }
}

namespace {

// §8.3, §9.7, §15.3 and §15.4: whether `name` names a class an instance of
// `mod` sees: one the module or the compilation unit declares, or one of the
// built-in classes.
bool NamesClass(const RtlirDesign& design, const RtlirModule& mod,
                std::string_view name) {
  static constexpr std::string_view kBuiltIn[] = {"process", "semaphore",
                                                  "mailbox"};
  const auto kIsNamed = [name](std::string_view cls) { return cls == name; };
  const auto kDeclares = [&](const std::vector<ClassDecl*>& decls) {
    return std::ranges::any_of(decls, [&](const ClassDecl* decl) {
      return decl != nullptr && kIsNamed(decl->name);
    });
  };
  return kDeclares(mod.class_decls) || kDeclares(design.cu_class_decls) ||
         std::ranges::any_of(kBuiltIn, kIsNamed);
}

}  // namespace

int VpiNamedTypeVariableKind(const RtlirDesign& design, const RtlirModule& mod,
                             std::string_view name) {
  if (design.type_targets.contains(name) || NamesClass(design, mod, name)) {
    return vpiClassVar;
  }
  const auto kFound = design.type_kinds.find(name);
  if (kFound == design.type_kinds.end()) return kVpiReg;
  return VpiDataTypeVariableKind(kFound->second);
}

namespace {

// §37.26: the member variable of `holder` the field `field` lays out: its
// vpiParent is the struct or union var, it is named after the field, its kind
// is the one a variable of the field's type has (§37.17), and its value is the
// field's bits of the holder's value, a copy that a read refreshes and a write
// is copied back from, read as a real where the field is one.
void MakeMember(VpiObject* holder, const StructFieldInfo& field,
                const RtlirDesign& design, const RtlirModule& mod,
                const VpiAttachBuild& build) {
  VpiObject* member = build.alloc();
  member->type = field.type_kind == DataTypeKind::kNamed
                     ? VpiNamedTypeVariableKind(design, mod, field.type_name)
                     : VpiDataTypeVariableKind(field.type_kind);
  member->parent = holder;
  member->name = build.keep(std::string(field.name));
  member->full_name = holder->full_name + "." + std::string(field.name);
  member->decl_signed = field.is_signed;
  auto* storage = build.arena.Create<Variable>();
  storage->value = MakeLogic4Vec(build.arena, field.width);
  storage->value.is_signed = field.is_signed;
  storage->value.is_real =
      member->type == vpiRealVar || member->type == vpiShortRealVar;
  member->var = storage;
  member->size = static_cast<int>(field.width);
  member->member_of = holder;
  member->member_offset = field.bit_offset;
  holder->children.push_back(member);
}

}  // namespace

void AttachStructMembers(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build) {
  // §37.17 details 3, 17 and 26: an unpacked struct or union var has a member
  // variable per field, the struct as its vpiParent and the field's value as
  // its own. The run keeps the whole struct as one variable, and no member
  // object was made, so vpiMember reached nothing and no name reached a field.
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : mod->variables) {
          const std::string kKey = VpiFlatName(prefix, var.name);
          VpiObject* holder = FindObjectForFlatName(objects, kKey);
          if (holder == nullptr || holder->var == nullptr ||
              (holder->type != vpiStructVar && holder->type != vpiUnionVar)) {
            continue;
          }
          const StructTypeInfo* info = ctx.GetVariableStructType(kKey);
          if (info == nullptr || info->is_packed) continue;
          for (const StructFieldInfo& field : info->fields) {
            MakeMember(holder, field, *design, *mod, build);
          }
        }
      });
}

}  // namespace delta
