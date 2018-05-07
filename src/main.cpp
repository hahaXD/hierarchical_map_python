//
// Created by Jason Shen on 4/22/18.
//
extern "C" {
#include <sddapi.h>
}
#include "cnf.h"
#include "optionparser.h"
#include <iostream>
#include <vector>
#include <src/psdd_manager.h>
#include <json.hpp>
#include <fstream>
#include <unordered_map>
#include <iostream>
using nlohmann::json;

struct Arg : public option::Arg {
  static void printError(const char *msg1, const option::Option &opt, const char *msg2) {
    fprintf(stderr, "%s", msg1);
    fwrite(opt.name, (size_t) opt.namelen, 1, stderr);
    fprintf(stderr, "%s", msg2);
  }

  static option::ArgStatus Required(const option::Option &option, bool msg) {
    if (option.arg != 0)
      return option::ARG_OK;

    if (msg) printError("Option '", option, "' requires an argument\n");
    return option::ARG_ILLEGAL;
  }

  static option::ArgStatus Numeric(const option::Option &option, bool msg) {
    char *endptr = 0;
    if (option.arg != 0 && strtol(option.arg, &endptr, 10)) {};
    if (endptr != option.arg && *endptr == 0)
      return option::ARG_OK;

    if (msg) printError("Option '", option, "' requires a numeric argument\n");
    return option::ARG_ILLEGAL;
  }
};

namespace {
std::unordered_map<int, std::vector<int>> ParseNodeToEdges(const char* node_to_edges_filename){
  std::ifstream data_input_stream(node_to_edges_filename);
  json data_input_json;
  data_input_stream >> data_input_json;
  std::unordered_map<int, std::vector<int>> result;
  for (auto it = data_input_json.begin(); it != data_input_json.end(); ++it){
    std::string node_index = it.key();
    std::vector<int> neighboring_edge_indexes;
    for (auto e_it = it.value().begin(); e_it != it.value().end(); ++ e_it){
      int cur_num = e_it;
      neighboring_edge_indexes.push_back(cur_num);
    }
    result[stoi(node_index)] = neighboring_edge_indexes;
  }
  return result;
}

SddNode* ExactlyOne(SddManager* sdd_manager, const std::vector<int>& variables){
  SddNode* result_node = sdd_manager_false(sdd_manager);
  for (int i  : variables){
    SddNode* cur_term = sdd_manager_true(sdd_manager);
    for (int j : variables){
      if (i!=j){
        cur_term = sdd_conjoin(sdd_manager_literal(-j, sdd_manager), cur_term, sdd_manager);
      }else{
        cur_term = sdd_conjoin(sdd_manager_literal(j, sdd_manager), cur_term, sdd_manager);
      }
    }
    result_node = sdd_disjoin(result_node, cur_term, sdd_manager);
  }
  return result_node;
}
}
enum optionIndex {
  UNKNOWN,
  HELP,
  CNF_EVID
};

const option::Descriptor usage[] =
    {
        {UNKNOWN, 0, "", "", option::Arg::None, "USAGE: example [options]\n\n \tOptions:"},
        {HELP, 0, "h", "help", option::Arg::None, "--help  \tPrint usage and exit."},
        {CNF_EVID, 0, "", "cnf_evid", Arg::Required, "--cnf_evid  evid file, represented using CNF."},
        {UNKNOWN, 0, "", "", option::Arg::None,
         "\nExamples:\n./psdd_inference  psdd_filename vtree_filename \n"},
        {0, 0, 0, 0, 0, 0}
    };

int main(int argc, const char *argv[]) {
  argc -= (argc > 0);
  argv += (argc > 0); // skip program name argv[0] if present
  option::Stats stats(usage, argc, argv);
  std::vector<option::Option> options(stats.options_max);
  std::vector<option::Option> buffer(stats.buffer_max);
  option::Parser parse(usage, argc, argv, &options[0], &buffer[0]);
  if (parse.error())
    return 1;
  if (options[HELP] || argc == 0) {
    option::printUsage(std::cout, usage);
    return 0;
  }
  const char *node_to_edge_indexes_filename = parse.nonOption(0);
  const char *psdd_filename = parse.nonOption(1);
  const char *vtree_filename = parse.nonOption(2);
  Vtree *vtree = sdd_vtree_read(vtree_filename);
  PsddManager *psdd_manager = PsddManager::GetPsddManagerFromVtree(vtree);
  sdd_vtree_free(vtree);
  PsddNode *result_node = psdd_manager->ReadPsddFile(psdd_filename, 0);
  if (options[CNF_EVID]) {
    auto cnf = new CNF(options[CNF_EVID].arg);
    PsddNode *psdd_constraint = cnf->Compile(psdd_manager, 0);
    auto posterior = psdd_manager->Multiply(psdd_constraint, result_node, 0);
    result_node = posterior.first;
    delete(cnf);
  }
  std::unordered_map<int, double> desination_probability;
  std::unordered_map<int, std::vector<int>> node_to_edge_indexes = ParseNodeToEdges(node_to_edge_indexes_filename);
  SddManager* sdd_manager = sdd_manager_new(vtree);
  sdd_manager_auto_gc_and_minimize_off(sdd_manager);
  std::unordered_map<uint32_t, uint32_t> identity_map;
  std::vector<SddLiteral> variables = vtree_util::VariablesUnderVtree(psdd_manager->vtree());
  for (SddLiteral cur_variable_index : variables){
    identity_map[(uint32_t)cur_variable_index] = (uint32_t)cur_variable_index;
  }
  for (auto n_it = node_to_edge_indexes.begin(); n_it != node_to_edge_indexes.end(); ++n_it){
    const auto& neighboring_edges = n_it->second;
    SddNode* cur_constraint = ExactlyOne(sdd_manager, neighboring_edges);
    PsddNode* cur_constraint_psdd = psdd_manager->ConvertSddToPsdd(cur_constraint, sdd_manager_vtree(sdd_manager), 0, identity_map);
    auto cur_result = psdd_manager->Multiply(cur_constraint_psdd, result_node, 0);
    desination_probability[n_it->first] = cur_result.second.parameter();
    sdd_manager_garbage_collect(sdd_manager);
    psdd_manager->DeleteUnusedPsddNodes({result_node});
  }
  std::cout << "Node distribution {";
  for (auto it = desination_probability.begin(); it != desination_probability.end(); ++it){
    std::cout << it->first << ":" << it->second << ",";
  }
  std::cout << "}" << std::endl;
  sdd_manager_free(sdd_manager);
  delete(psdd_manager);
}
