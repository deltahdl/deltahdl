#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
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

namespace {

// §37.17: the object kind of a member declared with `kind`, as a variable of
// that type would be; a logic var for a type §37.17 draws no box of its own
// for.
int MemberKind(DataTypeKind kind) {
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
    default:
      return kVpiReg;
  }
}

// §37.26: the member variable of `holder` the field `field` lays out: its
// vpiParent is the struct or union var, it is named after the field, and its
// value is the field's bits of the holder's value, a copy that a read
// refreshes and a write is copied back from.
void MakeMember(VpiObject* holder, const StructFieldInfo& field,
                const VpiAttachBuild& build) {
  VpiObject* member = build.alloc();
  member->type = MemberKind(field.type_kind);
  member->parent = holder;
  member->name = build.keep(std::string(field.name));
  member->full_name = holder->full_name + "." + std::string(field.name);
  member->decl_signed = field.is_signed;
  auto* storage = build.arena.Create<Variable>();
  storage->value = MakeLogic4Vec(build.arena, field.width);
  storage->value.is_signed = field.is_signed;
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
            MakeMember(holder, field, build);
          }
        }
      });
}

}  // namespace delta
