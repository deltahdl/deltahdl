#include "elaborator/viewport_resolution.h"

#include <cstddef>
#include <initializer_list>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/envelope_viewport.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

using PathParts = std::span<const std::string_view>;

// The components of a hierarchical name, split at each '.'.
std::vector<std::string_view> SplitPath(std::string_view name) {
  std::vector<std::string_view> parts;
  size_t start = 0;
  while (true) {
    const size_t kDot = name.find('.', start);
    parts.push_back(name.substr(start, kDot - start));
    if (kDot == std::string_view::npos) break;
    start = kDot + 1;
  }
  return parts;
}

// The components joined back into a hierarchical name.
std::string JoinPath(PathParts parts) {
  std::string path;
  for (std::string_view part : parts) {
    if (!path.empty()) path += '.';
    path += part;
  }
  return path;
}

// A component naming a block of a loop generate construct carries the index
// that selects it, `g[2]` (§27.4); the block is declared under `g`.
std::string_view BlockName(std::string_view part) {
  return part.substr(0, part.find('['));
}

// What resolving one viewport reads: the design's declarations and the
// envelope the viewport describes.
struct Envelope {
  const CompilationUnit& unit;
  const EnvelopeViewport& viewport;
  const SourceManager& sources;

  bool Holds(SourceLoc loc) const {
    return sources.StandsInEnvelope(loc, viewport);
  }

  // The module, interface or program the unit declares under `name`.
  const ModuleDecl* Element(std::string_view name) const {
    for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
      for (const ModuleDecl* decl : *list) {
        if (decl->name == name) return decl;
      }
    }
    return nullptr;
  }
};

bool ResolvesInElement(const ModuleDecl& decl, PathParts parts,
                       const Envelope& env);
bool ResolvesInItems(const std::vector<ModuleItem*>& items, PathParts parts,
                     const Envelope& env);

// An instance the envelope declares, and what follows its name: an item of the
// design element it instantiates, which the envelope must declare too for the
// item to be contained within it.
bool ResolvesThroughInstance(const ModuleItem& item, PathParts parts,
                             const Envelope& env) {
  if (item.inst_name != parts.front() || !env.Holds(item.loc)) return false;
  if (parts.size() == 1) return true;
  const ModuleDecl* decl = env.Element(item.inst_module);
  return decl != nullptr && env.Holds(decl->range.start) &&
         ResolvesInElement(*decl, parts.subspan(1), env);
}

// A generate construct and what follows a block's name: an item of that block.
// An if-generate's else branch is a construct of its own, and each case item
// holds a block of its own.
bool ResolvesThroughGenerate(const ModuleItem& item, PathParts parts,
                             const Envelope& env) {
  const std::string_view kBlock = BlockName(parts.front());
  if (item.name == kBlock && env.Holds(item.loc)) {
    return parts.size() == 1 ||
           ResolvesInItems(item.gen_body, parts.subspan(1), env);
  }
  for (const GenerateCaseItem& arm : item.gen_case_items) {
    if (arm.label == kBlock && parts.size() > 1 &&
        ResolvesInItems(arm.body, parts.subspan(1), env)) {
      return true;
    }
  }
  return item.gen_else != nullptr &&
         ResolvesThroughGenerate(*item.gen_else, parts, env);
}

// Whether `item` is, or leads to, the declaration `parts` names.
bool ResolvesThrough(const ModuleItem& item, PathParts parts,
                     const Envelope& env) {
  switch (item.kind) {
    case ModuleItemKind::kModuleInst:
      return ResolvesThroughInstance(item, parts, env);
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateFor:
    case ModuleItemKind::kGenerateCase:
      return ResolvesThroughGenerate(item, parts, env);
    default:
      return parts.size() == 1 && item.name == parts.front() &&
             env.Holds(item.loc);
  }
}

bool ResolvesInItems(const std::vector<ModuleItem*>& items, PathParts parts,
                     const Envelope& env) {
  for (const ModuleItem* item : items) {
    if (item != nullptr && ResolvesThrough(*item, parts, env)) return true;
  }
  return false;
}

// A port of the element, or an item it declares.
bool ResolvesInElement(const ModuleDecl& decl, PathParts parts,
                       const Envelope& env) {
  if (parts.size() == 1) {
    for (const PortDecl& port : decl.ports) {
      if (port.name == parts.front() && env.Holds(port.loc)) return true;
    }
  }
  return ResolvesInItems(decl.items, parts, env);
}

// The target `parts` names in `decl`: where the envelope declares the element
// itself, a name led by the element's own name; where the envelope stands
// inside it, a name of an item the envelope declares there.
std::optional<ViewportTarget> TargetIn(const ModuleDecl& decl, PathParts parts,
                                       const Envelope& env) {
  if (env.Holds(decl.range.start)) {
    if (parts.size() > 1 && parts.front() == decl.name &&
        ResolvesInElement(decl, parts.subspan(1), env)) {
      return ViewportTarget{decl.name, JoinPath(parts.subspan(1))};
    }
    return std::nullopt;
  }
  if (ResolvesInElement(decl, parts, env)) {
    return ViewportTarget{decl.name, JoinPath(parts)};
  }
  return std::nullopt;
}

}  // namespace

std::optional<ViewportTarget> ResolveViewport(const CompilationUnit& unit,
                                              const EnvelopeViewport& viewport,
                                              const SourceManager& sources) {
  const Envelope kEnv{unit, viewport, sources};
  const std::vector<std::string_view> kParts = SplitPath(viewport.object);
  for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* decl : *list) {
      auto target = TargetIn(*decl, kParts, kEnv);
      if (target) return target;
    }
  }
  return std::nullopt;
}

void ReportViewportsContainingNothing(const CompilationUnit& unit,
                                      DiagEngine& diag) {
  const SourceManager& sources = diag.Sources();
  for (const EnvelopeViewport& viewport : sources.Viewports()) {
    if (ResolveViewport(unit, viewport, sources)) continue;
    diag.Error(viewport.loc,
               "protect pragma viewport names \"" + viewport.object +
                   "\", which is not an object contained within its envelope",
               Subclause("34.5.32.2"));
  }
}

}  // namespace delta
