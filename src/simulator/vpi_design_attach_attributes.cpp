// §37.83: the attribute objects of a design, each the attribute instance
// (§5.12) elaboration resolved on the object it is a child of.

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §5.12: the value `attr` holds. One written with no value is a bit of 1; a
// string is the string it was written as; any other is the integer it folded
// to, at the width its expression is written with, or an integer's where the
// expression fixes none. Null for one whose value folded to no constant.
Variable* AttributeValue(const ResolvedAttribute& attr, Arena& arena) {
  if (attr.value != nullptr && attr.value->kind == ExprKind::kStringLiteral) {
    auto* storage = arena.Create<Variable>();
    storage->value = EvalStringLiteral(attr.value, arena);
    return storage;
  }
  if (!attr.resolved_value.has_value()) return nullptr;
  uint32_t width = attr.value == nullptr ? 1 : InferExprWidth(attr.value, {});
  if (width == 0) width = 32;
  auto* storage = arena.Create<Variable>();
  storage->value = MakeLogic4VecVal(
      arena, width, static_cast<uint64_t>(*attr.resolved_value));
  return storage;
}

// §37.83: the attributes a net or variable of the instance at `prefix` is
// written with, on the object the run's key for it made.
template <typename Declared>
void AttachDeclaredAttributes(const std::vector<Declared>& declared,
                              const std::string& prefix,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build) {
  for (const Declared& decl : declared) {
    VpiObject* obj =
        FindObjectForFlatName(objects, VpiFlatName(prefix, decl.name));
    if (obj != nullptr) VpiAttachAttributes(obj, decl.attrs, false, ctx, build);
  }
}

}  // namespace

const std::vector<ResolvedAttribute>& VpiNodeAttributes(
    const RtlirNodeAttributes* table, const void* node) {
  static const std::vector<ResolvedAttribute> kNone;
  if (table == nullptr) return kNone;
  const auto kFound = table->find(node);
  return kFound == table->end() ? kNone : kFound->second;
}

const std::vector<ResolvedAttribute>& VpiNodeAttributes(const RtlirModule* mod,
                                                        const void* node) {
  return VpiNodeAttributes(mod == nullptr ? nullptr : &mod->node_attrs, node);
}

void VpiAttachAttributes(VpiObject* owner,
                         const std::vector<ResolvedAttribute>& attrs,
                         bool on_definition, SimContext& ctx,
                         const VpiAttachBuild& build) {
  const SourceManager& sources = ctx.GetDiag().Sources();
  for (const ResolvedAttribute& attr : attrs) {
    VpiObject* obj = build.alloc();
    obj->type = vpiAttribute;
    obj->name = build.keep(std::string(attr.name));
    obj->def_attribute = on_definition;
    obj->var = AttributeValue(attr, build.arena);
    // The definition location is where the attribute instance was written,
    // restated where the preprocessor's joined text came from (§22.12).
    const SourceLoc kWritten = sources.ResolveToOrigin(attr.loc);
    obj->def_line_no = static_cast<int>(kWritten.line);
    obj->def_file = std::string(sources.FilePath(kWritten.file_id));
    obj->parent = owner;
    owner->children.push_back(obj);
  }
}

void AttachPortAttributes(const RtlirDesign* design,
                          const VpiObjectMap& objects, SimContext& ctx,
                          const VpiAttachBuild& build) {
  // §37.83: a port carries the attributes its declaration is written with.
  // Each port object holds the position its module declared it at.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string&, VpiObject* instance) {
        for (VpiObject* child : instance->children) {
          if (child->type != vpiPort) continue;
          const RtlirPort& port =
              mod->ports.at(static_cast<std::size_t>(child->index));
          VpiAttachAttributes(child, port.attrs, false, ctx, build);
        }
      });
}

void AttachAttributes(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build) {
  // §37.83: an instance carries the attributes its instantiation is written
  // with and, as attributes on its definition, those its module's declaration
  // is; a net or variable carries those it is declared with.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        VpiAttachAttributes(instance, mod->attrs, true, ctx, build);
        for (const RtlirModuleInst& child : mod->children) {
          VpiObject* obj = FindObjectForFlatName(
              objects, VpiFlatName(prefix, child.inst_name));
          if (obj != nullptr) {
            VpiAttachAttributes(obj, child.attrs, false, ctx, build);
          }
        }
        AttachDeclaredAttributes(mod->nets, prefix, objects, ctx, build);
        AttachDeclaredAttributes(mod->variables, prefix, objects, ctx, build);
      });
}

}  // namespace delta
