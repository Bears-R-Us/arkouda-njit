      
        proc ClusterKCoreDecomposition(ref passedMemebrs: domain(int), k: int): list(int) throws {
            writeln("////////////////************ KCoreDecomposition begin");

            // Initialize degrees array indexed by node IDs
            var nodes: [passedMemebrs] int = passedMemebrs;
            var degrees: [passedMemebrs] atomic int = 0;
                
            writeln("Initializing degrees array...");

            // Calculate degrees in parallel
            //forall idx in nodes.domain with (ref passedMemebrs) {
            for idx in nodes.domain {
                var deg = calculateDegree(passedMemebrs, nodes[idx]);
                degrees[idx].write(deg);
                writeln("Calculated degree for node ", nodes[idx], ": ", deg);
            }
            writeln("Degree calculation completed.\n");

            // Initialize activeNodes list with parallel safety
            var activeNodes: list(int, parSafe=true) = new list(int);
            writeln("Initialized activeNodes list.");

            // Find initial active nodes (degrees < k) in parallel
            writeln("Identifying initial active nodes (degrees < ", k, ")...");
            //forall idx in nodes with (ref activeNodes) {
            for idx in nodes {
                if (degrees[idx].read() < k) {
                    activeNodes.pushBack(nodes[idx]);
                    writeln("Initial active node found: ", nodes[idx]);
                }
            }
            writeln("Initial active nodes identification completed. activeNodes.size = ", activeNodes.size, "\n");

            // List to store new active nodes for the next iteration
            var newActiveNodes: list(int, parSafe=true) = new list(int);
            writeln("Initialized newActiveNodes list.\n");

            var iteration = 0;

            // Process active nodes until none remain
            while (activeNodes.size > 0) {
                iteration += 1;
                writeln("////////////////************ K-core Decomposition Iteration ", iteration);
                writeln("Current activeNodes.size = ", activeNodes.size);

                // Extract current batch of active nodes
                var currentBatch: list(int) = new list(int);
                writeln("Extracting currentBatch from activeNodes...");

                while (activeNodes.size > 0) {
                    var node = activeNodes.popBack();
                    currentBatch.pushBack(node);
                    writeln("Moved node ", node, " to currentBatch.");
                }
                writeln("Current batch size: ", currentBatch.size, "\n");

                // Process current batch in parallel
                writeln("Processing currentBatch in parallel...");
                //forall node in currentBatch with (ref newActiveNodes) {
                for node in currentBatch {
                    writeln("Processing node: ", node);

                    // Find neighbors of the node
                    var Neighbours: domain(int);
                    var inNeigh_elem = dstRG1[node]..<segRG1[node + 1];
                    var outNeigh_elem = dstNodesG1[node]..<segGraphG1[node + 1];
                    Neighbours += dstRG1[inNeigh_elem];
                    Neighbours += dstNodesG1[outNeigh_elem];

                    var valid_neis = Neighbours & passedMemebrs;
                    writeln("Node ", node, " has ", valid_neis.size, " valid neighbors.");

                    for neigh in valid_neis {
                        // Atomically decrement the degree
                        var oldDegree = degrees[neigh].fetchSub(1);
                        var newDegree = oldDegree - 1;
                        writeln("Node ", neigh, " degree decremented from ", oldDegree, " to ", newDegree);

                        // If new degree falls below k, add to newActiveNodes
                        if (newDegree < k) {
                            newActiveNodes.pushBack(neigh);
                            writeln("Node ", neigh, " added to newActiveNodes (new degree = ", newDegree, ")");
                        }
                    }
                }
                writeln("Processing of currentBatch completed.\n");

                // Swap activeNodes and newActiveNodes
                writeln("Swapping activeNodes and newActiveNodes.");
                activeNodes = newActiveNodes;
                newActiveNodes = new list(int, parSafe=true);
                writeln("activeNodes.size = ", activeNodes.size, ", newActiveNodes.size reset to 0.\n");
            }

            // After pruning, collect k-core nodes
            writeln("Collecting k-core nodes...");
            var kCoreNodes = new list(int);
            //forall elem in passedMemebrs with (ref kCoreNodes){
            for elem in passedMemebrs {
                if (degrees[elem].read() >= k) {
                    kCoreNodes.pushBack(elem);
                    writeln("Node ", elem, " is part of the k-core (degree = ", degrees[elem].read(), ")");
                }
            }
            writeln("kCoreNodes = ", kCoreNodes);
            return kCoreNodes;
        }
