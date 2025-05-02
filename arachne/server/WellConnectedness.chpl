module WellConnectedness {
	// Chapel modules.
  use Reflection;
  use Map;
  use List;
  use Set;
  use Random;
  use IO;
  use Time;
  use Sort;
  use Math;
  use Search;
  use CTypes;
  use CommDiagnostics;
  import CopyAggregation.SrcAggregator;
  import CopyAggregation.DstAggregator;
	import ChplConfig;

  // Arachne modules.
  import WellConnectedComponentsMsg.wccLogger;
	use BuildGraph;
  use GraphArray;
  use Utils;
  use ConnectedComponents;
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;
  use Logging;
	use ArgSortMsg;

	// Header and object files required for external C procedure calls
  require "viecut_helpers/computeMinCut.h",
          "viecut_helpers/computeMinCut.o",
          "viecut_helpers/logger.cpp.o",
					"leiden_helpers/computeLeiden.h",
          "leiden_helpers/computeLeiden.o",
          "-ligraph",
          "-llibleidenalg";
  
	// Function headers for external C procedure calls
	extern proc c_computeMinCut(partition_arr: [] int, src: [] int, dst: [] int, n: int, m: int): int;
  extern proc c_computeLeiden(src: [] int, dst: [] int, NumEdges: int, NumNodes: int,
	                            modularity_option: int, resolution: real, communities: [] int,
															numCommunities: int): int;

	// First-class functions specifying well-connectedness criterions
  proc log10Criterion(n:int, m:real) { return floor(log10(n:real)); }
  proc log2Criterion(n:int,  m:real) { return floor(log2(n:real)); }
  proc sqrtCriterion(n:int,  m:real) { return floor(sqrt(n:real)/5); }
  proc multCriterion(n:int,  m:real) { return floor(m*n:real); }

  /* Runs either WCC or CM dynamically choosing between shared-memory or distributed-memory 
	   implementations of both. */
	proc runWellConnectedness(G: SegGraph, st: borrowed SymTab, 
              							inputcluster_filePath: string, outputPath: string,
              							connectednessCriterion: string, connectednessCriterionMultValue: real, 
              							preFilterMinSize: int, postFilterMinSize: int): int throws {
    // Extract graph structural data, can be distributed or not depending on the type of array a is
		var srcNodesG = toSymEntry(G.getComp("SRC_SDI"), int).a;
    var dstNodesG = toSymEntry(G.getComp("DST_SDI"), int).a;
    var segGraphG = toSymEntry(G.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG = toSymEntry(G.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG = toSymEntry(G.getComp("NEIGHBORS_SET_SDI"), set(int)).a;

		// Variables needed for WCC or CM regardless if they are distributed or not
		var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
												else if connectednessCriterion == "log2" then log2Criterion
												else if connectednessCriterion == "sqrt" then sqrtCriterion
												else if connectednessCriterion == "mult" then multCriterion
												else log10Criterion;
		var newClusterIdToOriginalClusterId = new map(int,int);
		var newClusterId: atomic int = 0;

		// Variables needed for distributed WCC and CM
		var localeDom = blockDist.createDomain(0..<numLocales);
    var finalVerticesDistributed: [localeDom][{0..<1}] list(int, parSafe=true);
    var finalClustersDistributed: [localeDom][{0..<1}] list(int, parSafe=true);
    var newClusterIdDistributed: [localeDom][{0..<1}] chpl__processorAtomicType(int);
    coforall loc in Locales do on loc { newClusterIdDistributed[loc.id][0].write(1); }

		/* Reads in a tab-delimited file denoting vertices and the clusters they belong to. Returns a
		   map with original cluster identifier to a set of vertices that make up that cluster. */
		proc readClustersFile(filename: string) throws {
			var (vertices, clusters, _) = if ChplConfig.CHPL_COMM == "none" then 
																			readTSVFileLocal(filename,false);
																		else readTSVFileDistributed(filename,false);
			var combinedArray = makeDistArray((int,int), existingVertices.size);
			forall (c,i) in zip(combinedArray,combinedArray.domain) {
				c[0] = clusters[i];
				c[1] = vertices[i];
			}
			var iv = argsortDefault(combinedArray);
			var sortedVertices = vertices[iv];
			var sortedClusters = clusters[iv];

			var existingVertices = makeDistArray(vertices.size, bool);
			var internalVertices = makeDistArray(vertices.size, int);
			forall (v,i) in zip(sortedVertices,sortedVertices.domain) {
				const(found,idx) = binarySearch(nodeMapGraphG, v);
				if found {
					existingVertices[i] = true;
					internalVertices[i] = idx;
				}
			}
			var ivTruth = + scan existingVertices;
			var pop = ivTruth[ivTruth.size-1];
			var ivResize = makeDistArray(pop, int);
			forall ()
			
			var clustersMap: [localeDom]{0..<1} map(int, set(int, parSafe=true), parSafe=true);
			forall (ev,c) in zip(existingVertices, clusters) {
				if ev {
					var s = new set(int, parSafe=true);
					clustersMap.localAccess[here.id].add(c,s);
				}
			}

			return clustersMap;
		}
  }
}