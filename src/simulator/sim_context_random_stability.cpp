#include "simulator/sim_context_random_stability.h"

#include <cstdint>
#include <random>
#include <sstream>
#include <string>
#include <string_view>

#include "simulator/class_object.h"
#include "simulator/process.h"

namespace delta {

std::mt19937& RandomStability::ObjectRng(ClassObject* obj) {
  if (!obj->rng_initialized) {
    obj->rng.seed(obj->rng_seed);
    obj->rng_initialized = true;
  }
  return obj->rng;
}

void RandomStability::SeedObjectRng(ClassObject* obj, uint32_t seed) {
  obj->rng_seed = seed;
  obj->rng.seed(seed);
  obj->rng_initialized = true;
}

std::string RandomStability::GetRandState(ClassObject* obj) {
  std::ostringstream os;
  os << ObjectRng(obj);
  return os.str();
}

std::string RandomStability::GetRandState(Process* proc) {
  if (!proc->rng_initialized) {
    proc->rng.seed(proc->rng_seed);
    proc->rng_initialized = true;
  }
  std::ostringstream os;
  os << proc->rng;
  return os.str();
}

void RandomStability::SetRandState(ClassObject* obj, const std::string& state) {
  std::mt19937& gen = ObjectRng(obj);
  std::istringstream is(state);
  is >> gen;
  obj->rng_initialized = true;
}

std::mt19937& RandomStability::InitializationRng(std::string_view prefix,
                                                 uint32_t default_seed) {
  return init_rngs_.try_emplace(std::string(prefix), default_seed)
      .first->second;
}

void RandomStability::SetRandState(Process* proc, const std::string& state) {
  if (!proc->rng_initialized) {
    proc->rng.seed(proc->rng_seed);
    proc->rng_initialized = true;
  }
  std::istringstream is(state);
  is >> proc->rng;
}

}  // namespace delta
