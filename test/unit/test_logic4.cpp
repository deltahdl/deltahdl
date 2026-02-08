#include <catch2/catch_test_macros.hpp>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

TEST_CASE("Logic4Word basic values", "[types]") {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};
  Logic4Word z_val = {1, 1};

  REQUIRE(zero.is_known());
  REQUIRE(one.is_known());
  REQUIRE_FALSE(x_val.is_known());
  REQUIRE_FALSE(z_val.is_known());

  REQUIRE(zero.is_zero());
  REQUIRE(one.is_one());
  REQUIRE_FALSE(zero.is_one());
  REQUIRE_FALSE(one.is_zero());
}

TEST_CASE("Logic4Word AND operation", "[types]") {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  // 1 & 1 = 1
  auto r1 = logic4_and(one, one);
  REQUIRE(r1.aval == 1);
  REQUIRE(r1.bval == 0);

  // 1 & 0 = 0
  auto r2 = logic4_and(one, zero);
  REQUIRE(r2.aval == 0);
  REQUIRE(r2.bval == 0);

  // 0 & x = 0
  auto r3 = logic4_and(zero, x_val);
  REQUIRE(r3.aval == 0);
  REQUIRE(r3.bval == 0);

  // 1 & x = x
  auto r4 = logic4_and(one, x_val);
  REQUIRE(r4.bval != 0);
}

TEST_CASE("Logic4Word OR operation", "[types]") {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  // 0 | 0 = 0
  auto r1 = logic4_or(zero, zero);
  REQUIRE(r1.aval == 0);
  REQUIRE(r1.bval == 0);

  // 1 | 0 = 1
  auto r2 = logic4_or(one, zero);
  REQUIRE(r2.aval == 1);
  REQUIRE(r2.bval == 0);

  // 1 | x = 1
  auto r3 = logic4_or(one, x_val);
  REQUIRE(r3.aval == 1);
  REQUIRE(r3.bval == 0);
}

TEST_CASE("Logic4Word XOR operation", "[types]") {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};

  // 1 ^ 0 = 1
  auto r1 = logic4_xor(one, zero);
  REQUIRE(r1.aval == 1);
  REQUIRE(r1.bval == 0);

  // 1 ^ 1 = 0
  auto r2 = logic4_xor(one, one);
  REQUIRE(r2.aval == 0);
  REQUIRE(r2.bval == 0);
}

TEST_CASE("Logic4Word NOT operation", "[types]") {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  auto r1 = logic4_not(zero);
  REQUIRE(r1.aval == ~uint64_t(0));  // all 64 bits flip: 0→1
  REQUIRE(r1.bval == 0);

  auto r2 = logic4_not(one);
  REQUIRE(r2.aval == ~uint64_t(1));  // bit 0: 1→0, bits 1-63: 0→1
  REQUIRE(r2.bval == 0);

  auto r3 = logic4_not(x_val);
  REQUIRE(r3.bval != 0);
}

TEST_CASE("Logic4Vec creation and to_string", "[types]") {
  Arena arena;
  auto vec = make_logic4_vec_val(arena, 8, 0xA5);
  REQUIRE(vec.width == 8);
  REQUIRE(vec.is_known());
  REQUIRE(vec.to_uint64() == 0xA5);
  REQUIRE(vec.to_string() == "10100101");
}

TEST_CASE("Arena allocation", "[arena]") {
  Arena arena;
  auto* p1 = arena.alloc_array<uint64_t>(10);
  REQUIRE(p1 != nullptr);
  auto* p2 = arena.alloc_array<uint32_t>(100);
  REQUIRE(p2 != nullptr);
  REQUIRE(p1 != reinterpret_cast<uint64_t*>(p2));
  REQUIRE(arena.total_allocated() > 0);
}

TEST_CASE("Arena string allocation", "[arena]") {
  Arena arena;
  const char* src = "hello";
  auto* s = arena.alloc_string(src, 5);
  REQUIRE(std::string_view(s) == "hello");
}

TEST_CASE("Arena reset", "[arena]") {
  Arena arena;
  arena.alloc_array<char>(1000);
  REQUIRE(arena.total_allocated() == 1000);
  arena.reset();
  REQUIRE(arena.total_allocated() == 0);
}
