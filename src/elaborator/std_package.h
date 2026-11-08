#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

struct DataType;

enum class StdPackageMember : std::uint8_t {
  kSemaphore,
  kMailbox,
  kRandomize,
  kProcess,
  kWeakReference,
};

enum class StdPackageMemberKind : std::uint8_t { kClass, kFunction };

struct StdPackageEntry {
  StdPackageMember member = StdPackageMember::kSemaphore;
  std::string_view name;
  StdPackageMemberKind kind = StdPackageMemberKind::kClass;
  std::string_view defining_subclause;
  std::string_view prototype_subclause;
};

const std::vector<StdPackageEntry>& StdPackageContents();

std::string_view StdPackageMemberName(StdPackageMember member);
StdPackageMemberKind KindOfStdPackageMember(StdPackageMember member);
std::optional<StdPackageMember> StdPackageMemberNamed(std::string_view name);

std::string_view DefiningSubclauseOfStdPackageMember(StdPackageMember member);

std::string_view PrototypeSubclauseOfStdPackageMember(StdPackageMember member);
bool StdPackageDefinesSemanticsIn(StdPackageMember member,
                                  std::string_view subclause);

bool IsStdPackageSystemType(std::string_view name);

enum class StdMethodKind : std::uint8_t { kFunction, kTask };

struct StdFormal {
  std::string_view type;
  std::string_view name;
  bool has_default = false;
  bool by_reference = false;
};

struct StdMethodPrototype {
  std::string_view name;
  StdMethodKind kind = StdMethodKind::kFunction;
  std::string_view return_type;
  std::vector<StdFormal> formals;
  bool is_static = false;
  bool variadic = false;
};

const std::vector<StdMethodPrototype>& SemaphorePrototype();

const StdMethodPrototype& RandomizePrototype();

const std::vector<StdMethodPrototype>& MailboxPrototype();

const std::vector<StdMethodPrototype>& ProcessPrototype();

const std::vector<std::string_view>& ProcessStateEnumMembers();

const DataType* StdClassEnumType(const DataType& named);

bool StdClassIsFinal(StdPackageMember member);
bool StdClassHasConstructor(StdPackageMember member);

const std::vector<StdMethodPrototype>& WeakReferencePrototype();

struct StdTypeParameter {
  std::string_view name;
  std::string_view default_type;
  bool class_only = false;
};
std::optional<StdTypeParameter> StdClassTypeParameterOf(
    StdPackageMember member);

const std::vector<StdMethodPrototype>& StdClassPrototype(
    StdPackageMember member);

const StdMethodPrototype* StdMethodNamed(StdPackageMember member,
                                         std::string_view name);

std::size_t LeastActualsOf(const StdMethodPrototype& method);
std::size_t MostActualsOf(const StdMethodPrototype& method);

}  // namespace delta
