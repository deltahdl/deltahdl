#include <gtest/gtest.h>

#include <cstdint>
#include <cstdlib>

#include "helpers_open_array_natural_order.h"
#include "simulator/svdpi.h"

// Annex H.7.3 - Data representation.
//
// H.7.3 lists the additional restrictions DPI places on how SystemVerilog
// values are represented on the C side of the interface. Its enumerated claims
// and where each is realized:
//
//   1) SystemVerilog types that are neither packed nor contain packed elements
//      have a C-compatible representation. (own)
//   2) Basic integer and real types are represented as defined in H.7.4. (a
//      delegation to the satisfied dependency H.7.4 / Table H.1; not
//      re-proven.)
//   3) Packed types (time, integer, user-defined) use the canonical format of
//      H.7.7. (a delegation to the satisfied dependency H.7.7; not re-proven.)
//   4) Enumeration types are represented by the C representation of their
//      SystemVerilog base type; integer and time base types become 4-state
//      packed arrays; enumerated names are not available on the C side. (The
//      small-value classification (35.5.5) and the set of supported base types
//      (6.19, A.2.2.1) are delegated dependencies; the base-type representation
//      and the absence of names are H.7.3's own claims.)
//   5) An unpacked array embedded in a structure, and a stand-alone array
//   passed
//      to a sized formal, both have a C-compatible representation. (own)
//   6) For a stand-alone array passed to an open array formal: a 2-/4-state
//      scalar or packed element type is represented in canonical form; any
//      other element type is C compatible, in which case (shall) an element has
//      the same representation as an individual value of the same type,
//      reachable by normal C array indexing. (own)
//   7) (shall) The natural order of elements is used for each dimension of an
//      unpacked array - lower indices first. For a SystemVerilog range [L:R]
//      the element with index min(L,R) has C index 0 and the element with index
//      max(L,R) has C index abs(L-R). (own)
//
// These rules are realized entirely by existing production code, so the pass is
// test-only:
//   - C-compatible representation (claims 1, 5, 6-other) is carried by the
//     elem_size stride of SvOpenArrayDesc: an element sits at data +
//     i*elem_size, i.e. exactly where an individual value of that type would
//     sit in a plain C array, and svGetArrElemPtr* expose that address.
//   - Canonical form for packed/scalar open-array elements (claim 6-canonical)
//   is
//     carried by the canonical word storage: elem_size is 0 (the element
//     representation differs from an individual C value, so svGetArrElemPtr*
//     and svGetArrayPtr return null) while svPutBitArrElem1VecVal /
//     svGetBitArrElem1VecVal move the value through its canonical words.
//   - The 4-state canonical representation of an integer-base enum value (claim
//   4)
//     is carried by the canonical logic accessors svPutBitselLogic /
//     svGetBitselLogic.
//   - The natural element order (claim 7) is carried by svLow / svHigh /
//   svSize,
//     which report min(L,R) / max(L,R) / abs(L-R)+1 over a dimension's declared
//     bounds, so an element's C index is its SystemVerilog index minus svLow.
//
// Claim 7's range-mapping detail is also stated by the sibling subclause H.7.6,
// and the per-element addressing convention of the svGetArrElemPtr* family is
// defined by H.12.4; those concerns are owned and observed there. Here the
// natural-order layout coordinate is observed only through svLow / svHigh /
// svSize, the production that anchors min(L,R) at C index 0.

namespace {

svOpenArrayHandle MakeHandle(void* data, const SvOpenArrayDimRange* ranges,
                             int n_dims, size_t elem_size,
                             SvOpenArrayDesc* desc) {
  desc->data = data;
  desc->n_dims = n_dims;
  desc->ranges = ranges;
  desc->elem_size = elem_size;
  return desc;
}

// Claim 1: a stand-alone array of a non-packed type that contains no packed
// elements has a C-compatible representation. A plain C int has no packed part,
// so the descriptor records its natural byte stride (elem_size == sizeof(int))
// and each element is reached at data + i*elem_size - the same address an
// ordinary C int array would place it at. The value read back through that
// address is the individual int value, so the element representation is exactly
// the individual-value representation.
TEST(DataRepresentation, NonPackedTypeIsCCompatible) {
  int data[4] = {10, 20, 30, 40};
  const SvOpenArrayDimRange kRanges[] = {{31, 0},
                                         {0, 3}};  // int element, [0:3].
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, sizeof(int), &desc);

  for (int i = 0; i < 4; ++i) {
    void* p = svGetArrElemPtr1(h, i);
    EXPECT_EQ(p, static_cast<void*>(&data[i]));
    EXPECT_EQ(*static_cast<int*>(p),
              data[i]);  // element repr == individual int.
  }
}

// Claim 5: a stand-alone array passed to a sized formal (and, identically, an
// unpacked array embedded in a structure) has a C-compatible representation
// regardless of element type. Exercised with a non-packed double element: the
// elements occupy a contiguous C layout with the type's natural stride and the
// value at each slot is an ordinary double, so the representation matches a
// plain C double array element for element.
TEST(DataRepresentation, SizedFormalAndStructEmbeddedAreCCompatible) {
  double data[3] = {1.5, -2.25, 100.0};
  const SvOpenArrayDimRange kRanges[] = {{63, 0},
                                         {0, 2}};  // double element, [0:2].
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, sizeof(double), &desc);

  for (int i = 0; i < 3; ++i) {
    void* p = svGetArrElemPtr1(h, i);
    EXPECT_EQ(p, static_cast<void*>(&data[i]));
    EXPECT_EQ(*static_cast<double*>(p), data[i]);
  }
}

// Claim 6 (C-compatible branch, shall): when an open array's element type is
// not a 2-/4-state scalar or packed type, an element shall have the same
// representation as an individual value of the same type, and the elements are
// reachable by normal C array indexing. With a C-compatible element the stride
// equals sizeof(element), so consecutive elements are one element apart -
// exactly normal C pointer arithmetic - and reading a slot yields the
// individual value stored there.
TEST(DataRepresentation, OpenArrayCCompatibleElementMatchesIndividualValue) {
  int data[5] = {0, 11, 22, 33, 44};
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {0, 4}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, sizeof(int), &desc);

  int* base = static_cast<int*>(svGetArrElemPtr1(h, 0));
  ASSERT_EQ(base, &data[0]);
  for (int i = 0; i < 5; ++i) {
    // Normal C array indexing off the first element reaches every element, and
    // each is the same int representation as an individual value.
    EXPECT_EQ(&base[i], static_cast<int*>(svGetArrElemPtr1(h, i)));
    EXPECT_EQ(base[i], data[i]);
  }
  // The element stride is one whole element, the individual-value size.
  EXPECT_EQ(static_cast<char*>(svGetArrElemPtr1(h, 1)) -
                static_cast<char*>(svGetArrElemPtr1(h, 0)),
            static_cast<long>(sizeof(int)));
}

// Claim 6 (canonical branch): a packed (or 2-/4-state scalar) element type is
// represented in canonical form rather than as an individual C value. The
// descriptor marks this by recording elem_size 0, which signals that the
// element representation differs from an individual value of the same type.
// Production then refuses the C-pointer views - svGetArrElemPtr* and
// svGetArrayPtr return null - while the canonical element accessors move the
// value through its canonical words.
TEST(DataRepresentation, OpenArrayPackedElementUsesCanonicalForm) {
  // Element is logic [7:0] -> one canonical word; four such elements, [0:3].
  svBitVecVal data[4] = {0u, 0u, 0u, 0u};
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, /*elem_size=*/0, &desc);

  // Canonical, not C-compatible: no individual-value address and no whole-array
  // C address are available.
  EXPECT_EQ(svGetArrElemPtr1(h, 0), nullptr);
  EXPECT_EQ(svGetArrayPtr(h), nullptr);

  // The value still round-trips through its canonical word representation.
  const svBitVecVal kIn = 0xA5u;
  svPutBitArrElem1VecVal(h, &kIn, 2);
  EXPECT_EQ(data[2], 0xA5u);  // canonical word for element [2].
  svBitVecVal out = 0u;
  svGetBitArrElem1VecVal(&out, h, 2);
  EXPECT_EQ(out, 0xA5u);
}

// Claim 6 (canonical branch, scalar half / edge): a 2-/4-state scalar element
// type is also represented in canonical form, not as an individual C value. A
// single logic element occupies one canonical word whose bit 0 carries the
// four-state value, so elem_size is 0 (no individual-value address) and the
// value moves through the canonical scalar accessors. All four logic states
// round-trip, confirming the representation is the 4-state canonical one.
TEST(DataRepresentation, OpenArrayScalarElementUsesCanonicalForm) {
  svLogicVecVal data[4] = {{0u, 0u}, {0u, 0u}, {0u, 0u}, {0u, 0u}};
  const SvOpenArrayDimRange kRanges[] = {{0, 0},
                                         {0, 3}};  // logic scalar, [0:3].
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, /*elem_size=*/0, &desc);

  // Canonical, not C-compatible: no individual-value element address.
  EXPECT_EQ(svGetArrElemPtr1(h, 1), nullptr);
  EXPECT_EQ(svGetArrayPtr(h), nullptr);

  const svLogic kStates[] = {sv_0, sv_1, sv_z, sv_x};
  for (svLogic s : kStates) {
    svPutLogicArrElem1(h, s, 1);
    EXPECT_EQ(svGetLogicArrElem1(h, 1), s);  // 4-state canonical round-trip.
  }
}

// Claim 6 (canonical branch, multi-word edge): a packed element wider than one
// canonical 32-bit word is still represented in canonical form, spanning as
// many canonical words as the element width requires. A logic [39:0] element
// occupies two canonical words; the value round-trips across both words while
// the individual-value C address remains unavailable (elem_size 0).
TEST(DataRepresentation, OpenArrayWidePackedElementUsesCanonicalForm) {
  // Two elements of a 40-bit packed type: two canonical words each.
  svBitVecVal data[4] = {0u, 0u, 0u, 0u};
  const SvOpenArrayDimRange kRanges[] = {{39, 0},
                                         {0, 1}};  // [39:0] element, [0:1].
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, /*elem_size=*/0, &desc);

  EXPECT_EQ(svGetArrElemPtr1(h, 0), nullptr);

  const svBitVecVal kIn[2] = {0x12345678u,
                              0x9Au};  // 40-bit value over two words.
  svPutBitArrElem1VecVal(h, kIn, 1);
  EXPECT_EQ(data[2], 0x12345678u);  // element [1] low canonical word.
  EXPECT_EQ(data[3], 0x9Au);        // element [1] high canonical word.

  svBitVecVal out[2] = {0u, 0u};
  svGetBitArrElem1VecVal(out, h, 1);
  EXPECT_EQ(out[0], 0x12345678u);
  EXPECT_EQ(out[1], 0x9Au);
}

// Claim 4: an enumeration is represented by the C representation of its
// SystemVerilog base type, and an integer base type is represented as a 4-state
// packed array. An integer-base enum value is therefore carried as the
// canonical 4-state packed value of the underlying integer, identical to
// representing that plain integer - the canonical logic accessors place the
// value's bits, and no enumerator name accompanies it. The named constant
// exists only in SystemVerilog; the C side sees the numeric base value alone.
TEST(DataRepresentation, EnumRepresentedByBaseTypeWithoutNames) {
  // An enum value whose SystemVerilog enumerator label is irrelevant to C: only
  // its integer base value (here 0x2C) crosses, as a 4-state packed value.
  const uint32_t kBaseValue = 0x2Cu;

  svLogicVecVal as_enum = {0u, 0u};
  svLogicVecVal as_integer = {0u, 0u};
  for (int bit = 0; bit < 32; ++bit) {
    svLogic v = ((kBaseValue >> bit) & 1u) ? sv_1 : sv_0;
    svPutBitselLogic(&as_enum, bit, v);
    svPutBitselLogic(&as_integer, bit, v);
  }

  // The enum value's representation is bit-for-bit the representation of its
  // integer base value (4-state packed, all bits 0/1), carrying no name data.
  EXPECT_EQ(as_enum.aval, as_integer.aval);
  EXPECT_EQ(as_enum.bval, as_integer.bval);
  EXPECT_EQ(as_enum.aval, kBaseValue);
  EXPECT_EQ(as_enum.bval, 0u);  // a defined integer base value: no x/z bits.
  for (int bit = 0; bit < 32; ++bit) {
    EXPECT_EQ(svGetBitselLogic(&as_enum, bit),
              svGetBitselLogic(&as_integer, bit));
  }
}

// Claim 4 (time base edge): a time base type is represented as a 4-state packed
// array too, and time is 64 bits wide, so its canonical representation spans
// two canonical words. A time-base enum value is therefore carried bit-for-bit
// as the canonical 4-state representation of the underlying 64-bit base value,
// across both words, with no enumerator name attached.
TEST(DataRepresentation, EnumTimeBaseRepresentedAsWide4State) {
  const uint64_t kBaseValue = (static_cast<uint64_t>(0x100u) << 32) | 0x2Cu;

  svLogicVecVal as_enum[2] = {{0u, 0u}, {0u, 0u}};
  svLogicVecVal as_time[2] = {{0u, 0u}, {0u, 0u}};
  for (int bit = 0; bit < 64; ++bit) {
    svLogic v = ((kBaseValue >> bit) & 1u) ? sv_1 : sv_0;
    svPutBitselLogic(as_enum, bit, v);  // bit/32 selects the canonical word.
    svPutBitselLogic(as_time, bit, v);
  }

  // The enum representation matches its time base value, word for word, with no
  // x/z bits and no name data.
  EXPECT_EQ(as_enum[0].aval, as_time[0].aval);
  EXPECT_EQ(as_enum[1].aval, as_time[1].aval);
  EXPECT_EQ(as_enum[0].aval, 0x2Cu);   // low word of the 64-bit base value.
  EXPECT_EQ(as_enum[1].aval, 0x100u);  // high word.
  EXPECT_EQ(as_enum[0].bval, 0u);
  EXPECT_EQ(as_enum[1].bval, 0u);
  for (int bit = 0; bit < 64; ++bit) {
    EXPECT_EQ(svGetBitselLogic(as_enum, bit), svGetBitselLogic(as_time, bit));
  }
}

// Claim 7 (shall): the natural element order is used per unpacked dimension,
// lower indices first, so for a SystemVerilog range [L:R] the element with
// index min(L,R) has C index 0 and the element with index max(L,R) has C index
// abs(L-R). svLow / svHigh / svSize report min / max / count over the declared
// bounds, and an element's C index is its SystemVerilog index minus svLow.
// Exercised for an ascending, a descending, and a negative range.
TEST(DataRepresentation, UnpackedNaturalOrderMinToZeroMaxToAbs) {
  struct Case {
    int l;
    int r;
  };
  const Case kCases[] = {{0, 7}, {7, 0}, {-1, -8}};
  for (const Case& c : kCases) {
    const SvOpenArrayDimRange kRanges[] = {{0, 0},
                                           {c.l, c.r}};  // dim 1 under test.
    SvOpenArrayDesc desc;
    svOpenArrayHandle h = MakeHandle(nullptr, kRanges, 2, 0, &desc);

    ExpectUnpackedNaturalOrderMinToZeroMaxToAbs(h, 1, c.l, c.r);
  }
}

// Claim 7 (single-element edge): a dimension declared [k:k] has abs(L-R) == 0,
// so min(L,R) and max(L,R) coincide and the sole element maps to C index 0. The
// natural-order formula degenerates correctly even for a negative declared
// index, where svLow / svHigh report the coincident bound and svSize reports a
// unit count.
TEST(DataRepresentation, UnpackedSingleElementDimensionMapsToZero) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0},
                                         {-4, -4}};  // unpacked [-4:-4].
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(nullptr, kRanges, 2, 0, &desc);

  EXPECT_EQ(svLow(h, 1), -4);
  EXPECT_EQ(svHigh(h, 1), -4);
  EXPECT_EQ(svSize(h, 1), 1);
  EXPECT_EQ(svHigh(h, 1) - svLow(h, 1), 0);  // sole element -> C index 0.
}

// Claim 7 "lower indices go first": walking the SystemVerilog indices of a
// declared range from low to high yields contiguous C indices 0, 1, 2, ...,
// independent of the declared orientation. Verified against a descending,
// negative-spanning declaration [3:-2].
TEST(DataRepresentation, UnpackedLowerIndicesGoFirst) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {3, -2}};  // unpacked [3:-2].
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(nullptr, kRanges, 2, 0, &desc);

  const int kLo = svLow(h, 1);     // -2
  const int kSize = svSize(h, 1);  // 6
  EXPECT_EQ(kLo, -2);
  EXPECT_EQ(kSize, 6);

  int expected_c = 0;
  for (int sv = kLo; sv < kLo + kSize; ++sv) {
    EXPECT_EQ(sv - kLo,
              expected_c);  // ascending SV index -> 0,1,2,... C indices.
    ++expected_c;
  }
  EXPECT_EQ(expected_c, kSize);
}

}  // namespace
