#include <string>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// §37.50: the object kind of the concurrent assertion `item` writes, by its
// keyword.
int ConcurrentKindOf(const ModuleItem& item) {
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

// §37.50: the object the concurrent assertion `item` stands as in `scope`,
// named by its label, reporting where it stands and, for a cover, whether it
// covers a sequence.
void MakeConcurrentAssertion(const ModuleItem& item, VpiObject* scope,
                             SimContext& ctx, const VpiAttachBuild& build) {
  VpiObject* obj = build.alloc();
  obj->type = ConcurrentKindOf(item);
  obj->parent = scope;
  if (!item.name.empty()) {
    obj->name = build.keep(std::string(item.name));
    obj->full_name = VpiScopedFullName(scope, item.name);
  }
  obj->cover_sequence = item.kind == ModuleItemKind::kCoverSequence;
  VpiRecordAssertionLocation(obj, SourceRange{item.loc, item.end}, ctx);
  scope->children.push_back(obj);
}

}  // namespace

void VpiRecordAssertionLocation(VpiObject* obj, const SourceRange& range,
                                SimContext& ctx) {
  // §37.49: where the assertion stands - its file, the line and column it
  // starts at and those it ends at - read where the text was written (§22.12).
  // A position the parser did not record leaves its pair as it was.
  const SourceManager& sources = ctx.GetDiag().Sources();
  if (range.start.IsValid()) {
    const SourceLoc kStart = sources.ResolveToOrigin(range.start);
    obj->file = std::string(sources.FilePath(kStart.file_id));
    obj->start_line = static_cast<int>(kStart.line);
    obj->column = static_cast<int>(kStart.column);
  }
  if (range.end.IsValid()) {
    const SourceLoc kEnd = sources.ResolveToOrigin(range.end);
    obj->end_line = static_cast<int>(kEnd.line);
    obj->end_column = static_cast<int>(kEnd.column);
  }
}

void AttachAssertions(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build) {
  // §37.49 with §39.3.1 step b: an instance reaches the assertions written as
  // its items, each hung from the generate block instance that writes it
  // (§37.12), or from the instance itself. A deferred immediate one runs as a
  // process the elaborator makes of it, whose walk (AttachProcedures) builds
  // it as the statement it is, with its parts (§37.55).
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string&, VpiObject* instance) {
        for (const RtlirAssertion& assertion : mod->assertions) {
          const ModuleItem* item = assertion.item;
          if (item == nullptr ||
              (item->body != nullptr && item->body->is_deferred)) {
            continue;
          }
          VpiObject* scope = VpiGenScopeOf(instance, assertion.gen_block_path);
          if (scope != nullptr) {
            MakeConcurrentAssertion(*item, scope, ctx, build);
          }
        }
      });
}

}  // namespace delta
