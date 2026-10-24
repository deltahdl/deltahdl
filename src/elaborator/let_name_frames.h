#pragma once

#include <cstdint>
#include <deque>
#include <span>
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
  // A class's: the frames of the classes it extends (§8.13, §8.26.2), whose
  // members it inherits, searched before the scope around it.
  std::vector<const NameFrame*> bases;
};

// The binding `name` has at `frame`, from the frame itself or the nearest one
// around it holding the name, a class's frame holding what it inherits; null
// where none does.
const NameBinding* FindName(const NameFrame& frame, std::string_view name);

// The binding the scope of `frame` itself declares for `name`, or a class
// inherits, null for a name it imports or does not hold, and for a null frame.
const NameBinding* FindOwnName(const NameFrame* frame, std::string_view name);

// The hops a chain of typedef names is followed through. A longer chain, as a
// cycle of names makes one, is left unfollowed.
inline constexpr int kMaxTypedefHops = 32;

// The type the typedef `named` declares, null where `named` is null, no
// typedef's, or an interface port's (§25.10), whose type the interface the
// port connects declares.
const DataType* TypedefTypeOf(const NameBinding* named);

// The frame of each package of a compilation unit (§26.2), its declarations
// over its imports' names. A package may import only a package written before
// it, so each is built from those before it. The built-in package std
// (§26.7), which no source declares, has a frame of the names Annex G gives
// it, unless the unit declares a package of that name itself.
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
  NameFrame std_{nullptr};
};

// The frame of each class a type is named through (§8.23), built the first
// time it is asked for: the names the class declares, over those it inherits
// from the classes it extends, within the frame of the scope declaring it,
// which a name the class neither declares nor inherits is looked up in. And
// the declarations the names of types reach through those frames, the
// packages' (§26.3) and `unit`, the compilation unit's (§3.12.1).
class ClassFrames {
 public:
  ClassFrames(const PackageFrames& packages, const NameFrame& unit)
      : packages_(packages), unit_(unit) {}

  // The frame a type named through `cls`, declared in the scope of
  // `declaring`, is followed in. A class with parameters has none, as its
  // typedefs may stand for the values a specialization gives.
  const NameFrame* Of(const ClassDecl& cls, const NameFrame& declaring);

  // The frame of what `cls` declares and inherits, whether or not it has
  // parameters, which a name written in the class is looked up in. None where
  // a class it extends has no frame (Of), or one this cannot find.
  const NameFrame* MembersOf(const ClassDecl& cls, const NameFrame& declaring);

  // The declaration a type's name reaches, written in the scope of `scope`: a
  // bare name through the scopes around it, and a name behind prefixes the
  // one the scope they name declares. `$unit` names the compilation unit's
  // scope; a first prefix names a class the scopes around `scope` see under
  // that name (§8.23), else the package of that name; and each later prefix
  // names a class the scope before it declares, so that `C::t`, `p::C::t`
  // and `Outer::Inner::t` each reach the typedef the class declares. Null
  // where a prefix names none, or a class with no frame.
  const NameBinding* TypeName(const DataType& type, const NameFrame& scope);

  // MembersOf the class a type's prefixes end in, `P` of `P#(4)::t`, followed
  // through typedefs naming it (§8.25), where a name written in that class is
  // looked up; null where they end in no class. The type is one written with
  // prefixes.
  const NameFrame* PrefixClassMembers(const DataType& type,
                                      const NameFrame& scope);

 private:
  const NameBinding* Named(std::span<const std::string_view> prefixes,
                           std::string_view name, const NameFrame& scope);
  const NameFrame* ScopeNamed(std::span<const std::string_view> prefixes,
                              const NameFrame& scope);
  const NameFrame* OutermostScope(std::string_view prefix,
                                  const NameFrame& scope);
  const NameFrame* ClassFrame(const NameBinding* named);
  const NameBinding* ThroughTypedefs(const NameBinding* named);
  const NameFrame* BaseFrame(std::string_view name, std::string_view scope,
                             const NameFrame& declaring);

  const PackageFrames& packages_;
  const NameFrame& unit_;
  std::deque<NameFrame> frames_;
  std::unordered_map<const ClassDecl*, const NameFrame*> built_;
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

// §6.10: the implicit nets the scope of `items`, filled in `frame`, declares.
// A name that a primitive's terminal list, an instance's port connections, an
// alias or a continuous assignment's target writes alone, and that no scope
// the use reaches declares, is a scalar net of the default net type, of the
// scope it is written in.
void DeclareImplicitNets(NameFrame& frame,
                         const std::vector<ModuleItem*>& items);

// The names a design element's header declares: its ports and its parameter
// ports.
void DeclareHeader(NameFrame& frame, const ModuleDecl& decl);

// The scope a subroutine's or a block's statements `stmts`, none of them null,
// make: their imports and their declarations.
void DeclareStatements(NameFrame& frame, const std::vector<Stmt*>& stmts,
                       const PackageFrames& packages);

// The names `s` declares for its own statements and expressions: a block's
// declarations, a for loop's variables and a foreach loop's.
void DeclareStatementScope(NameFrame& frame, const Stmt* s,
                           const PackageFrames& packages);

}  // namespace delta
