#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/LiteralIndex.hpp"
#include <chrono>

#include "SATSubsumption/ForwardBenchmarkWrapper.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

static std::chrono::high_resolution_clock::duration totalDuration = chrono::duration<int64_t, std::nano>::zero();
static ofstream outputFile;
static ofstream problemFile;

ForwardBenchmarkWrapper::ForwardBenchmarkWrapper(bool subsumptionResolution) : _forwardBenchmark(subsumptionResolution), _forwardOracle(subsumptionResolution), _subsumptionResolution(subsumptionResolution)
{
}

ForwardBenchmarkWrapper::~ForwardBenchmarkWrapper()
{
}

void ForwardBenchmarkWrapper::attach(SaturationAlgorithm *salg)
{
  ForwardSimplificationEngine::attach(salg);
  _unitIndex = static_cast<UnitClauseLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE));
  _fwIndex = static_cast<FwSubsSimplifyingLiteralIndex *>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE));

  _forwardBenchmark.attach(salg);
  _forwardOracle.attach(salg);

  // replace the '.' with '_' in the file name
  vstring problemName = env.options->problemName();
  for (unsigned i = 0; i < problemName.length(); i++) {
    if (problemName[i] == '.') {
      problemName[i] = '_';
    }
  }
  vstring fileName = "outputs/" + env.options->problemName();
#if SAT_SR_IMPL == 0
  fileName += "_no_sat";
#elif SAT_SR_IMPL == 1
  fileName += "_direct";
#elif SAT_SR_IMPL == 2
  fileName += "_indirect";
#elif SAT_SR_IMPL == 3
  fileName += "_dynamic";
#else
  fileName += "_unknown";
#endif
#if USE_OPTIMIZED_FORWARD
  fileName += "_opt";
#endif
#if !CORRELATE_LENGTH_TIME
  cout << "Opening file " << fileName << endl;
  outputFile.open(fileName.c_str());
#endif
}

void ForwardBenchmarkWrapper::detach()
{
  _forwardBenchmark.detach();
  _forwardOracle.detach();
  _unitIndex = nullptr;
  _fwIndex = nullptr;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

bool ForwardBenchmarkWrapper::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  replacement = nullptr;
  premises = ClauseIterator::getEmpty();

  /* First measure the time for the method */
  ClauseIterator premiseAux;
  Clause *replacementAux = nullptr;
#if !CORRELATE_LENGTH_TIME
  auto start = chrono::high_resolution_clock::now();
#endif
  bool resultAux = _forwardBenchmark.perform(cl, replacementAux, premiseAux);
#if !CORRELATE_LENGTH_TIME
  auto stop = chrono::high_resolution_clock::now();

  auto duration = chrono::duration_cast<chrono::microseconds>(stop - start);
  totalDuration += duration;
  outputFile << duration.count() << endl;
#endif

  /* Then compute the output using the oracle */
  auto start_oracle = chrono::high_resolution_clock::now();
  bool result = _forwardOracle.perform(cl, replacement, premises);
  auto stop_oracle = chrono::high_resolution_clock::now();
  auto duration_oracle = chrono::duration_cast<chrono::microseconds>(stop_oracle - start_oracle);

  const double threshold = 5;
  bool enable_symmetric = false;
  if ((false && duration_oracle.count() > threshold * duration.count() && duration_oracle.count() > 500)
  ||  (enable_symmetric && duration_oracle.count() * threshold < duration.count() && duration.count() > 500)) {
    string file_name = "log/oracle_faster_instances.txt";
    if (duration_oracle.count() > duration.count()) {
      file_name = "log/oracle_slower_instances.txt";
    }

    // open to append at the end of the file
    ofstream log_file(file_name, ios_base::app);
    log_file << "------------------------------------------------------------" << endl;
    log_file << "Configuration: ";
#if SAT_SR_IMPL == 0
    log_file << "no_sat";
#elif SAT_SR_IMPL == 1
    log_file << "direct";
#elif SAT_SR_IMPL == 2
    log_file << "indirect";
#elif SAT_SR_IMPL == 3
    log_file << "dynamic";
#else
    log_file << "unknown";
#endif
#if USE_OPTIMIZED_FORWARD
    log_file << " optimized";
#endif
    log_file << endl;
    log_file << "Problem: " << env.options->problemName() << endl;
    log_file << "duration of the method: " << duration.count() << endl;
    log_file << "duration of the oracle: " << duration_oracle.count() << endl;
    log_file << "result: " << resultAux << endl;
    log_file << "replacement: " << (replacement == nullptr ? "nullptr" : replacement->toString()) << endl;
    log_file << "cl: " << cl->toString() << endl;

    DHSet<Clause *>  seen;
    for (unsigned li = 0; li < cl->length(); li++) {
      Literal *lit = (*cl)[li];
      auto it = _fwIndex->getGeneralizations(lit, false, false);
      while (it.hasNext()) {
        Clause *mcl = it.next().clause;
        if (!seen.insert(mcl)) {
          continue;
        }
        log_file << "positive generalizations: " << mcl->toString() << endl;
      }
    }
    for (unsigned li = 0; li < cl->length(); li++) {
      Literal *lit = (*cl)[li];
      auto it = _fwIndex->getGeneralizations(lit, true, false);
      while (it.hasNext()) {
        Clause *mcl = it.next().clause;
        if (!seen.insert(mcl)) {
          continue;
        }
        seen.insert(mcl);
        log_file << "complementary generalizations: " << mcl->toString() << endl;
      }
    }

    log_file.close();
  }

  if (result != resultAux || (replacement == nullptr) != (replacementAux == nullptr)) {
    if (!problemFile.is_open()) {
      vstring fileName = "log/mistakes_" + env.options->problemName() + ".txt";
      problemFile.open(fileName.c_str());
    }
    problemFile << "------------------------------------------------------------" << endl;
    problemFile << "Configuration: ";
#if SAT_SR_IMPL == 0
    problemFile << "no_sat";
#elif SAT_SR_IMPL == 1
    problemFile << "direct";
#elif SAT_SR_IMPL == 2
    problemFile << "indirect";
#elif SAT_SR_IMPL == 3
    problemFile << "dynamic";
#else
    problemFile << "unknown";
#endif
#if USE_OPTIMIZED_FORWARD
    problemFile << " optimized";
#endif
    problemFile << endl;
    problemFile << "ForwardBenchmarkWrapper::perform: result != resultAux" << endl;
    problemFile << "result: " << result << endl;
    problemFile << "resultAux: " << resultAux << endl;
    problemFile << "cl:             " << *cl << endl;
    if (result) {
      problemFile << "premises:       ";
      while (premises.hasNext()) {
        Clause *mcl = premises.next();
        problemFile << *mcl << endl;
      }
    }
    else {
      problemFile << "premises Aux:   " << endl;
      while (premiseAux.hasNext()) {
        problemFile << *premiseAux.next() << endl;
      }
    }
    if (replacement) {
      problemFile << "replacement:    " << *replacement << endl;
    }
    if (replacementAux) {
      problemFile << "replacementAux: " << *replacementAux << endl;
    }
  }
  return result;
}

void ForwardBenchmarkWrapper::printStats(std::ostream &out)
{
  out << "**** ForwardBenchmarkWrapper ****" << endl;
  out << "Total time for perform: " << ((double)totalDuration.count() / 1000000000) << " seconds" << endl;
#if !CORRELATE_LENGTH_TIME
  outputFile.close();
#endif
  if (problemFile.is_open()) {
    problemFile.close();
  }
}
