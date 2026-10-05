#include <string>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// §37.49 with §16.4: the immediate assertion kind of a deferred assertion
// statement of `kind`.
int ImmediateKindOf(StmtKind kind) {
  if (kind == StmtKind::kAssumeImmediate) return vpiImmediateAssume;
  return kind == StmtKind::kCoverImmediate ? vpiImmediateCover
                                           : vpiImmediateAssert;
}

// §37.49 and §37.50: the object kind of the assertion `item` writes - a
// deferred immediate one by the statement the parser wraps it around, and a
// concurrent one by its keyword.
int AssertionKindOf(const ModuleItem& item) {
  if (item.body != nullptr && item.body->is_deferred) {
    return ImmediateKindOf(item.body->kind);
  }
  switch (item.kind) {
    case ModuleItemKind::kAssumeProperty:
      return vpiAssume;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      return vpiCover;
    case ModuleItemKind::kRestrictProperty:
      return vpiRestrict;
    default:
      return vpiAssert;
  }
}

// §37.49: where the assertion written at `loc` stands - its file, and the line
// and column it starts at - read where the text was written (§22.12). A
// position the parser did not record leaves all three as they were.
void RecordAssertionLocation(VpiObject* obj, SourceLoc loc,
                             const SourceManager& sources) {
  if (!loc.IsValid()) return;
  const SourceLoc kWritten = sources.ResolveToOrigin(loc);
  obj->file = std::string(sources.FilePath(kWritten.file_id));
  obj->start_line = static_cast<int>(kWritten.line);
  obj->column = static_cast<int>(kWritten.column);
}

}  // namespace

void AttachAssertions(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build) {
  // §37.49 with §39.3.1 step b: an instance reaches the assertions written as
  // its items, each of the kind it is, named by its label (§37.50), reporting
  // where it stands, and a cover reporting whether it covers a sequence.
  // RtlirModule::assertions kept each, and no pass made an object of one, so
  // vpi_iterate(vpiAssertion) reached none in any design.
  const SourceManager& sources = ctx.GetDiag().Sources();
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string&, VpiObject* instance) {
        for (const ModuleItem* item : mod->assertions) {
          if (item == nullptr) continue;
          VpiObject* obj = build.alloc();
          obj->type = AssertionKindOf(*item);
          obj->parent = instance;
          if (!item->name.empty()) {
            obj->name = build.keep(std::string(item->name));
            obj->full_name = VpiScopedFullName(instance, item->name);
          }
          obj->cover_sequence = item->kind == ModuleItemKind::kCoverSequence;
          RecordAssertionLocation(obj, item->loc, sources);
          instance->children.push_back(obj);
        }
      });
}

}  // namespace delta
