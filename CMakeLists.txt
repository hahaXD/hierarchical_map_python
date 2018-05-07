cmake_minimum_required(VERSION 3.9)
project(hierarchical_map)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_C_STANDARD 99)
include_directories(src lib/psdd lib/psdd/lib/googletest/googletest/include lib/psdd/lib/googletest/googlemock/include lib/psdd/lib/libsdd/ lib/psdd/lib/json/include/nlohmann lib/psdd/lib/json/include)
add_subdirectory(lib/psdd)

file(GLOB HIERARCHICAL_MAP_SRC_FILES "src/*.h" "src/*.cpp" "src/*.c")
add_executable(hierarchical_exp ${HIERARCHICAL_MAP_SRC_FILES} src/main.cpp)
target_link_libraries(hierarchical_exp structured_bn psdd sdd nlohmann_json gmp)
