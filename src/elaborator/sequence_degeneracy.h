#pragma once

#include <cstdint>

namespace delta {

enum class SequenceMatchClass : uint8_t {
  kAdmitsNoMatch,
  kAdmitsOnlyEmpty,
  kAdmitsAtLeastOneNonempty,
  kAdmitsBothEmptyAndNonempty,
};

bool IsDegenerate(SequenceMatchClass m);
bool IsNondegenerate(SequenceMatchClass m);
bool AdmitsAnyEmptyMatch(SequenceMatchClass m);

enum class SequenceUsageContext : uint8_t {
  kAsProperty,
  kOverlappingImplicationAntecedent,
  kNonoverlappingImplicationAntecedent,
};

bool IsSequenceUsageLegal(SequenceUsageContext ctx, SequenceMatchClass m);

}  // namespace delta
