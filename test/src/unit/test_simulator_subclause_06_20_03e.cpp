#include <gtest/gtest.h>

#include "helpers_instance_type_procedures.h"

namespace {

constexpr InstanceTypeSpelling kTypeParameter{"type T = int", "T", "T", ""};

TEST(ProceduralTypeParameterSim, EachInstanceDeclaresItsLocalsWithItsType) {
  ExpectEachInstanceTakesItsType(kTypeParameter, {"byte", "int", "shortint"},
                                 ByteIntShortintExpected());
}

TEST(ProceduralTypeParameterSim, GenerateLoopInstancesTakeTheirOwnTypes) {
  ExpectEachLoopInstanceTakesItsType(kTypeParameter, "T(logic [4*i+3:0])");
}

}  // namespace
