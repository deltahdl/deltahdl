#pragma once

#include <cstdint>
#include <deque>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

namespace delta {

struct ClassDecl;
struct CompilationUnit;
struct DataType;
struct Expr;
struct ImportItem;
struct ModuleDecl;
struct ModuleItem;
struct PackageDecl;
struct Stmt;

// What a name a scope declares or imports stands for, as far as the check of
// a let's actuals (§11.12, rule 2) reads it: a let a call may name, a variable
// an actual may name, a typedef or a class a type may name, or any other
// declaration, which only hides the names of the scopes around it.
enum class NameKind : std::uint8_t {
  kLet,
  kVariable,
  kTypedef,
  kClass,
  kOther
};

struct NameFrame;

// One name's declaration. `scope` is the frame of the scope declaring it,
// where the names its type and dimensions are written with are looked up; a
// name an import brings in keeps its package's frame.
struct NameBinding {
  NameKind kind = NameKind::kOther;
  // The let or typedef declared.
  const ModuleItem* item = nullptr;
  // The class declared.
  const ClassDecl* cls = nullptr;
  // A variable's declared type and its unpacked dimensions, null for none.
  const DataType* type = nullptr;
  const std::vector<Expr*>* dims = nullptr;
  const NameFrame* scope = nullptr;
};

// The names one scope declares or imports, and the frame of the scope around
// it, which a name the scope does not hold is looked up in (§23.9). A binding
// a frame holds for a name of its own scope's declaration names the frame as
// its scope; one an import brought in names the package's. A frame is filled
// in place and never copied, as its bindings point at it.
struct NameFrame {
  explicit NameFrame(const NameFrame* enclosing) : outer(enclosing) {}
  NameFrame(const NameFrame&) = delete;
  NameFrame& operator=(const NameFrame&) = delete;

  const NameFrame* outer;
  std::unordered_map<std::string_view, NameBinding> names;
  // Set by a wildcard import of a package no frame was built for, any of
  // whose names the scope may then hold.
  bool imports_unknown = false;
};

// The binding `name` has at `frame`, from the frame itself or the nearest one
// around it holding the name; null where none does, or where a frame on the
// way imports a package whose names are not known.
const NameBinding* FindName(const NameFrame& frame, std::string_view name);

// The binding the scope of `frame` itself declares for `name`, null for a name
// it imports or does not hold, and for a null frame.
const NameBinding* FindOwnName(const NameFrame* frame, std::string_view name);

// The frame of each package of a compilation unit (§26.2), its declarations
// over its imports' names. A package may import only a package written before
// it, so each is built from those before it.
class PackageFrames {
 public:
  explicit PackageFrames(const CompilationUnit* unit);
  // The frame of the package named `package`, null for none.
  const NameFrame* Find(std::string_view package) const;
  const std::vector<std::pair<const PackageDecl*, const NameFrame*>>& All()
      const {
    return packages_;
  }

 private:
  std::deque<NameFrame> frames_;
  std::vector<std::pair<const PackageDecl*, const NameFrame*>> packages_;
};

// Declares `name`, when there is one, as a declaration other than a let, a
// variable, a typedef or a class.
void DeclareOther(NameFrame& frame, std::string_view name);

// Fills `frame` with what a scope of `items` holds (§26.3): the names its
// wildcard imports make candidates, under those its explicit imports bring
// in, under its own declarations. The items of a generate block among them
// belong to the block's own frame.
void DeclareScope(NameFrame& frame, const std::vector<ModuleItem*>& items,
                  const PackageFrames& packages);

// The compilation unit's scope (§3.12.1): the scope of `items`, the unit's
// items in view, and the classes the unit declares.
void DeclareUnitScope(NameFrame& frame, const std::vector<ModuleItem*>& items,
                      const CompilationUnit& unit,
                      const PackageFrames& packages);

// The names a design element's header declares: its ports and its parameter
// ports.
void DeclareHeader(NameFrame& frame, const ModuleDecl& decl);

// The scope a subroutine's or a block's statements `stmts` make: their
// imports and their declarations.
void DeclareStatements(NameFrame& frame, const std::vector<Stmt*>& stmts,
                       const PackageFrames& packages);

// The names `s` declares for its own statements and expressions: a block's
// declarations, a for loop's variables and a foreach loop's.
void DeclareStatementScope(NameFrame& frame, const Stmt* s,
                           const PackageFrames& packages);

}  // namespace delta
