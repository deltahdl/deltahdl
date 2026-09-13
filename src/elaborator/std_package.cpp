#include "elaborator/std_package.h"

#include <cstddef>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

const std::vector<StdPackageEntry>& StdPackageContents() {
  // §G.1: the semaphore class, the mailbox class, the randomize function, the
  // process class and the weak reference class, in that order.
  // §G.2: each with the subclause its prototype in §G.3 through §G.7 names as
  // defining its semantics.
  static const std::vector<StdPackageEntry> kContents{
      {StdPackageMember::kSemaphore, "semaphore", StdPackageMemberKind::kClass,
       "15.3", "G.3"},
      {StdPackageMember::kMailbox, "mailbox", StdPackageMemberKind::kClass,
       "15.4", "G.4"},
      {StdPackageMember::kRandomize, "randomize",
       StdPackageMemberKind::kFunction, "18.12", "G.5"},
      {StdPackageMember::kProcess, "process", StdPackageMemberKind::kClass,
       "9.7", "G.6"},
      {StdPackageMember::kWeakReference, "weak_reference",
       StdPackageMemberKind::kClass, "8.30", "G.7"},
  };
  return kContents;
}

std::string_view StdPackageMemberName(StdPackageMember member) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.member == member) return entry.name;
  }
  return {};
}

StdPackageMemberKind KindOfStdPackageMember(StdPackageMember member) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.member == member) return entry.kind;
  }
  return StdPackageMemberKind::kClass;
}

std::optional<StdPackageMember> StdPackageMemberNamed(std::string_view name) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.name == name) return entry.member;
  }
  return std::nullopt;
}

std::string_view DefiningSubclauseOfStdPackageMember(StdPackageMember member) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.member == member) return entry.defining_subclause;
  }
  return {};
}

std::string_view PrototypeSubclauseOfStdPackageMember(StdPackageMember member) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.member == member) return entry.prototype_subclause;
  }
  return {};
}

bool StdPackageDefinesSemanticsIn(StdPackageMember member,
                                  std::string_view subclause) {
  // §G.2: the indicated subclause, or one beneath it -- "8.30.1" lies in
  // "8.30" where "8.301" does not.
  const std::string_view kDefining =
      DefiningSubclauseOfStdPackageMember(member);
  if (subclause == kDefining) return true;
  return subclause.size() > kDefining.size() &&
         subclause.substr(0, kDefining.size()) == kDefining &&
         subclause[kDefining.size()] == '.';
}

bool IsStdPackageSystemType(std::string_view name) {
  const std::optional<StdPackageMember> kMember = StdPackageMemberNamed(name);
  return kMember &&
         KindOfStdPackageMember(*kMember) == StdPackageMemberKind::kClass;
}

const std::vector<StdMethodPrototype>& SemaphorePrototype() {
  // §G.3: class semaphore; function new(int keyCount = 0); function void
  // put(int keyCount = 1); task get(int keyCount = 1); function int
  // try_get(int keyCount = 1); endclass.
  static const std::vector<StdMethodPrototype> kPrototype{
      {"new", StdMethodKind::kFunction, "", {{"int", "keyCount", true}}},
      {"put", StdMethodKind::kFunction, "void", {{"int", "keyCount", true}}},
      {"get", StdMethodKind::kTask, "void", {{"int", "keyCount", true}}},
      {"try_get", StdMethodKind::kFunction, "int", {{"int", "keyCount", true}}},
  };
  return kPrototype;
}

const StdMethodPrototype& RandomizePrototype() {
  // §G.5: function int randomize( ... ).
  static const StdMethodPrototype kPrototype{
      "randomize", StdMethodKind::kFunction, "int", {}, false, true};
  return kPrototype;
}

const std::vector<StdMethodPrototype>& MailboxPrototype() {
  // §G.4: class mailbox #(type T = dynamic_singular_type); function new(int
  // bound = 0); function int num(); task put(T message); function int
  // try_put(T message); task get(ref T message); function int try_get(ref T
  // message); task peek(ref T message); function int try_peek(ref T
  // message); endclass.
  static const std::vector<StdMethodPrototype> kPrototype{
      {"new", StdMethodKind::kFunction, "", {{"int", "bound", true}}},
      {"num", StdMethodKind::kFunction, "int", {}},
      {"put", StdMethodKind::kTask, "void", {{"T", "message"}}},
      {"try_put", StdMethodKind::kFunction, "int", {{"T", "message"}}},
      {"get", StdMethodKind::kTask, "void", {{"T", "message", false, true}}},
      {"try_get",
       StdMethodKind::kFunction,
       "int",
       {{"T", "message", false, true}}},
      {"peek", StdMethodKind::kTask, "void", {{"T", "message", false, true}}},
      {"try_peek",
       StdMethodKind::kFunction,
       "int",
       {{"T", "message", false, true}}},
  };
  return kPrototype;
}

const std::vector<StdMethodPrototype>& ProcessPrototype() {
  // §G.6: class :final process; typedef enum {FINISHED, RUNNING, WAITING,
  // SUSPENDED, KILLED} state; static function process self(); function state
  // status(); function void kill(); task await(); function void suspend();
  // function void resume(); function void srandom(int seed); function string
  // get_randstate(); function void set_randstate(string state); endclass.
  static const std::vector<StdMethodPrototype> kPrototype{
      {"self", StdMethodKind::kFunction, "process", {}, true},
      {"status", StdMethodKind::kFunction, "state", {}},
      {"kill", StdMethodKind::kFunction, "void", {}},
      {"await", StdMethodKind::kTask, "void", {}},
      {"suspend", StdMethodKind::kFunction, "void", {}},
      {"resume", StdMethodKind::kFunction, "void", {}},
      {"srandom", StdMethodKind::kFunction, "void", {{"int", "seed"}}},
      {"get_randstate", StdMethodKind::kFunction, "string", {}},
      {"set_randstate",
       StdMethodKind::kFunction,
       "void",
       {{"string", "state"}}},
  };
  return kPrototype;
}

const std::vector<std::string_view>& ProcessStateEnumMembers() {
  static const std::vector<std::string_view> kMembers{
      "FINISHED", "RUNNING", "WAITING", "SUSPENDED", "KILLED"};
  return kMembers;
}

bool StdClassIsFinal(StdPackageMember member) {
  // §G.6: class :final process; the other prototypes carry no :final.
  return member == StdPackageMember::kProcess;
}

bool StdClassHasConstructor(StdPackageMember member) {
  return StdMethodNamed(member, "new") != nullptr;
}

std::optional<StdTypeParameter> StdClassTypeParameterOf(
    StdPackageMember member) {
  switch (member) {
    case StdPackageMember::kMailbox:
      // §G.4: #(type T = dynamic_singular_type).
      return StdTypeParameter{"T", "dynamic_singular_type", false};
    case StdPackageMember::kSemaphore:
    case StdPackageMember::kRandomize:
    case StdPackageMember::kProcess:
    case StdPackageMember::kWeakReference:
      return std::nullopt;
  }
  return std::nullopt;
}

const std::vector<StdMethodPrototype>& StdClassPrototype(
    StdPackageMember member) {
  static const std::vector<StdMethodPrototype> kNone;
  switch (member) {
    case StdPackageMember::kSemaphore:
      return SemaphorePrototype();
    case StdPackageMember::kMailbox:
      return MailboxPrototype();
    case StdPackageMember::kProcess:
      return ProcessPrototype();
    case StdPackageMember::kRandomize:
    case StdPackageMember::kWeakReference:
      return kNone;
  }
  return kNone;
}

const StdMethodPrototype* StdMethodNamed(StdPackageMember member,
                                         std::string_view name) {
  for (const StdMethodPrototype& method : StdClassPrototype(member)) {
    if (method.name == name) return &method;
  }
  return nullptr;
}

std::size_t LeastActualsOf(const StdMethodPrototype& method) {
  std::size_t least = 0;
  for (const StdFormal& formal : method.formals) {
    if (!formal.has_default) ++least;
  }
  return least;
}

std::size_t MostActualsOf(const StdMethodPrototype& method) {
  return method.formals.size();
}

}  // namespace delta
