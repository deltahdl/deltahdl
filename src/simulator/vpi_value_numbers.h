#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

// §38.15, Table 38-3: the integer value of `v`, its x and z bits read as 0,
// and sign-extended from its width when `v` is signed, so a negative value of
// a signed object narrower than 64 bits reads as negative.
int64_t VpiKnownIntegerValue(const Logic4Vec& v);

// §38.15: the format vpiObjTypeVal resolves to for an object of `type` read
// as the type it is -- vpiIntVal for an integer variable, vpiTimeVal for a time
// variable -- or vpiObjTypeVal where the value's bits choose it.
int VpiObjTypeFormat(int type);

}  // namespace delta
