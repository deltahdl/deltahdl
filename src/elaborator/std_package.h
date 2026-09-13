#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

// §G.1: the built-in standard package, std, has the contents Annex G
// describes -- the semaphore class, the mailbox class, the randomize
// function, the process class and the weak reference class -- each with a
// prototype of its own in §G.3 through §G.7. §G.2 adds that the package
// contains system types, the types of §26.7's std package, and that the
// semantics of each of its members are defined not in the annex but in the
// subclause its prototype indicates: §15.3 for semaphore, §15.4 for mailbox,
// §18.12 for randomize, §9.7 for process and §8.30 for weak_reference. This
// file is the one place the contents are written down: the compilation-unit
// scope registers the std package's class names from it, and any other
// reader of the std package asks it what the package holds and where each
// member's semantics live.

// §G.1: the five members, in the order the subclause lists them.
enum class StdPackageMember : std::uint8_t {
  kSemaphore,
  kMailbox,
  kRandomize,
  kProcess,
  kWeakReference,
};

// §G.1: four of the members are classes and one, randomize, is a function.
enum class StdPackageMemberKind : std::uint8_t { kClass, kFunction };

struct StdPackageEntry {
  StdPackageMember member = StdPackageMember::kSemaphore;
  std::string_view name;
  StdPackageMemberKind kind = StdPackageMemberKind::kClass;
  std::string_view defining_subclause;   // §G.2: where the semantics are
  std::string_view prototype_subclause;  // §G.3 to §G.7: where the prototype is
};

// §G.1: the contents of the std package, in the subclause's order.
const std::vector<StdPackageEntry>& StdPackageContents();

// §G.1: the name a member is declared under in the std package, its kind,
// and the member a name denotes, or none where the std package holds no
// member of that name.
std::string_view StdPackageMemberName(StdPackageMember member);
StdPackageMemberKind KindOfStdPackageMember(StdPackageMember member);
std::optional<StdPackageMember> StdPackageMemberNamed(std::string_view name);

// §G.2: the subclause the semantics of a member are defined in, which the
// member's prototype in §G.3 through §G.7 indicates; and whether a subclause
// lies there, being that subclause or one beneath it, so that a diagnostic a
// std member's semantics raise can be seen to cite the place §G.2 points to.
std::string_view DefiningSubclauseOfStdPackageMember(StdPackageMember member);

// §G.3 through §G.7: the subclause of the annex that gives a member's
// prototype, which a diagnostic checking a call against the prototype cites.
std::string_view PrototypeSubclauseOfStdPackageMember(StdPackageMember member);
bool StdPackageDefinesSemanticsIn(StdPackageMember member,
                                  std::string_view subclause);

// §G.2: the std package contains system types; a name denotes one iff it
// denotes a member of the package that is a class, randomize being a function
// and no type.
bool IsStdPackageSystemType(std::string_view name);

// §G.3 through §G.7 give each class of the std package a prototype: its
// methods, each a function or a task, with a return type and formals of which
// some carry a default, and with the constructor new among them where the
// class has one. A prototype is written down once here and read by the
// elaborator where a call on a handle of the class is checked against it.
enum class StdMethodKind : std::uint8_t { kFunction, kTask };

struct StdFormal {
  std::string_view type;
  std::string_view name;
  bool has_default = false;
};

struct StdMethodPrototype {
  std::string_view name;
  StdMethodKind kind = StdMethodKind::kFunction;
  std::string_view return_type;  // void for a task and a void function
  std::vector<StdFormal> formals;
  bool is_static = false;
};

// §G.3: the prototype of the semaphore class -- new(int keyCount = 0),
// void put(int keyCount = 1), task get(int keyCount = 1) and
// int try_get(int keyCount = 1).
const std::vector<StdMethodPrototype>& SemaphorePrototype();

// The prototype of a member of the std package: empty for the randomize
// function, which is no class, and for a class whose prototype is not
// written down.
const std::vector<StdMethodPrototype>& StdClassPrototype(
    StdPackageMember member);

// The method of a std class of the given name, or null where the prototype
// declares none.
const StdMethodPrototype* StdMethodNamed(StdPackageMember member,
                                         std::string_view name);

// A call of a method may pass no fewer actuals than the formals without a
// default and no more than the formals there are.
std::size_t LeastActualsOf(const StdMethodPrototype& method);
std::size_t MostActualsOf(const StdMethodPrototype& method);

}  // namespace delta
