#pragma once

#include <cstdint>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>

#include "simulator/class_object.h"
#include "simulator/sim_context_types.h"

namespace delta {

class RandomStability {
 public:
  std::mt19937& ObjectRng(ClassObject* obj);

  void SeedObjectRng(ClassObject* obj, uint32_t seed);

  std::string GetRandState(ClassObject* obj);

  std::string GetRandState(Process* proc);

  void SetRandState(ClassObject* obj, const std::string& state);

  void SetRandState(Process* proc, const std::string& state);

  int32_t* RandomSeed() { return &random_seed_; }

  std::mt19937& InitializationRng(std::string_view prefix,
                                  uint32_t default_seed);

 private:
  int32_t random_seed_ = 0;
  std::unordered_map<std::string, std::mt19937> init_rngs_;
};

}  // namespace delta
