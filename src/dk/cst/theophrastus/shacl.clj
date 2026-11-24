(ns dk.cst.theophrastus.shacl
  "SHACL validation of a db, with the report as Clojure data.

  See https://www.w3.org/TR/shacl/"
  (:require [dk.cst.theophrastus :as theo]
            [dk.cst.theophrastus.convert :as convert]
            [dk.cst.theophrastus.impl.owl :as owl]
            [dk.cst.theophrastus.term :as term]
            [dk.cst.theophrastus.txn :as txn])
  (:import [org.apache.jena.graph Graph GraphMemFactory GraphUtil Node]
           [org.apache.jena.query Dataset Query]
           [org.apache.jena.rdf.model Model]
           [org.apache.jena.shacl ShaclValidator Shapes ValidationReport]
           [org.apache.jena.shacl.engine Target TargetType ValidationContext]
           [org.apache.jena.shacl.lib ShLib]
           [org.apache.jena.shacl.parser Shape]
           [org.apache.jena.shacl.validation ReportEntry VLib]
           [org.apache.jena.shacl.vocabulary SHACL]
           [org.apache.jena.sparql.core Var]
           [org.apache.jena.sparql.exec QueryExec]
           [org.apache.jena.sparql.path P_Link Path]
           [org.apache.jena.sparql.syntax ElementAssign ElementBind ElementData
            ElementMinus ElementService ElementSubQuery ElementVisitorBase
            ElementWalker]
           [org.apache.jena.system G]))

(defn- shapes-graph
  "The Graph of the shapes in `x`, as parse takes them."
  ^Graph [x]
  (cond
    (instance? Shapes x) (.getGraph ^Shapes x)
    (instance? Graph x)  x
    (instance? Model x)  (.getGraph ^Model x)
    ;; a copy, since a db of TDB2 can only be read in a transaction
    (map? x)             (txn/calculate-read
                           x
                           #(doto (GraphMemFactory/createDefaultGraph)
                              (GraphUtil/addInto (theo/jena-graph x))))
    (coll? x)            (let [g (GraphMemFactory/createDefaultGraph)]
                           (doseq [y x]
                             (GraphUtil/addInto g (shapes-graph y)))
                           g)
    :else                (-> (theo/db {:transactional? false})
                             (theo/read! x)
                             (theo/jena-graph))))

(defn parse
  "The Jena Shapes in `x`: a db, a Graph, a Model, Jena Shapes, a source as
  theo/read! takes it, or a coll of these, whose shapes are merged."
  ^Shapes [x]
  (if (instance? Shapes x)
    x
    (Shapes/parse (shapes-graph x))))

(def owl-restrictions
  "The kinds of OWL restriction that owl-shapes can make shapes of."
  #{:min-cardinality :max-cardinality :some-values-from :all-values-from
    :has-value})

(defn owl-shapes
  "A db of SHACL shapes for the OWL restrictions in the ontology `db`, with
  these `opts`:

  - :restrictions, the kinds of restriction to make shapes of (all but
    :some-values-from when not given):
    - :min-cardinality, owl:minCardinality and the least of owl:cardinality,
      and their qualified forms
    - :max-cardinality, owl:maxCardinality and the most of owl:cardinality,
      and their qualified forms
    - :some-values-from, owl:someValuesFrom
    - :all-values-from, owl:allValuesFrom
    - :has-value, owl:hasValue
  - :severity, the severity of their results, e.g. :sh/Warning
    (:sh/Violation when not given)

  Validating data against the shapes checks the restrictions under the
  closed-world assumption, as Aristotle's validators did. The shapes follow
  the class and property hierarchies, inverses and ranges of the ontology,
  so the data needn't hold the ontology or come from a reasoner.

  A restriction that has no named class, or whose filler is a datatype
  restriction, gets no shape. For the consistency checks of a reasoner, see
  rules/validate."
  ([db]
   (owl-shapes db nil))
  ;; not owl:someValuesFrom by default, since an ontology often uses it to
  ;; say that something exists rather than that the data has it, e.g. that
  ;; each expression of the semiotics pattern that OntoLex imports expresses
  ;; a meaning
  ([db {:keys [restrictions severity]
        :or   {restrictions (disj owl-restrictions :some-values-from)}
        :as   opts}]
   (when-let [unknown (seq (remove owl-restrictions restrictions))]
     (throw (ex-info (str "Not a kind of restriction: " (first unknown))
                     {:restrictions restrictions})))
   (let [prefixes (merge (:prefixes db)
                         term/default-prefixes
                         {:sh "<http://www.w3.org/ns/shacl#>"})
         ontology (assoc db :prefixes prefixes)
         shapes   (txn/with-read-transaction ontology
                    (vec (for [kind  (sort restrictions)
                               row   (owl/restrictions ontology kind)
                               :let  [shape (owl/shape ontology kind row)]
                               :when shape]
                           (cond-> shape
                             severity (assoc-in [:sh/property :sh/severity]
                                                severity)))))]
     (theo/transact! (theo/db {:prefixes prefixes :transactional? false})
                     shapes))))

(defn- entry->map
  "The map of the report entry `e`, with `prefixes` for keywords."
  [^ReportEntry e prefixes]
  (let [value #(some-> ^Node % (convert/data prefixes))]
    {:focus-node           (value (.focusNode e))
     :path                 (let [^Path path (.resultPath e)]
                             (if (instance? P_Link path)
                               (value (.getNode ^P_Link path))
                               (some-> path str)))
     :value                (value (.value e))
     :source-shape         (value (.source e))
     :constraint-component (value (.sourceConstraintComponent e))
     :message              (.message e)
     :severity             (some-> (.severity e) (.level) value)}))

;; SHACL, section 3.6: a validation report has a result for each failure,
;; with its focus node, path, value, source shape, constraint component and
;; severity
(defn- report->map
  "The map of the validation `report`, with `prefixes` for keywords."
  [^ValidationReport report prefixes]
  {:conforms? (.conforms report)
   :results   (mapv #(entry->map % prefixes) (.getEntries report))})

;; SHACL, sections 3.1 and 3.3
(defn- linked-shapes
  "The named graphs of `db` that make up the shapes graph of its data, as
  views of them: those that it names with sh:shapesGraph, and those that
  they import, transitively."
  [{:keys [^Dataset dataset prefixes] :as db}]
  (let [db     (assoc db :prefixes (assoc prefixes
                                     :sh "<http://www.w3.org/ns/shacl#>"
                                     :owl "<http://www.w3.org/2002/07/owl#>"))
        named? #(.containsNamedModel dataset
                                     ^String (term/iri % (:prefixes db)))
        links  (map '?g (theo/q db "SELECT DISTINCT ?g WHERE {
                                      ?s sh:shapesGraph ?g FILTER (isIRI(?g))
                                    }"))]
    (cond
      (empty? links)
      (throw (ex-info "The db names no shapes graph with sh:shapesGraph" {}))

      (nil? dataset)
      (throw (ex-info "A Model has no named graphs for its shapes graphs"
                      {:shapes-graphs links}))

      (not-every? named? links)
      (throw (ex-info (str "Not a named graph of the db: "
                           (pr-str (first (remove named? links))))
                      {:shapes-graphs links}))

      :else
      (loop [todo (vec links) seen #{}]
        (if-let [g (first todo)]
          (if (seen g)
            (recur (subvec todo 1) seen)
            (let [imports (->> (theo/q (theo/named-graph db g)
                                       "SELECT DISTINCT ?i WHERE {
                                          ?x owl:imports ?i FILTER (isIRI(?i))
                                        }")
                               (map '?i)
                               (filter named?))]
              (recur (into (subvec todo 1) imports) (conj seen g))))
          (mapv #(theo/named-graph db %) seen))))))

;; SHACL, appendix A, has the rules for a query with a pre-bound variable.
;; A VALUES for other variables is let through, since it binds nothing here.
(defn- pre-bindable?
  "Whether the SELECT `query` of a target has the same answer for one node
  when ?this is pre-bound to it as when it's run in full.

  It has, unless it binds ?this itself (with VALUES, BIND or AS), has a
  MINUS, a SERVICE, a LIMIT or an OFFSET, or has a subquery that doesn't
  return ?this."
  [^Query query]
  (let [?this   (Var/alloc "this")
        fine?   (volatile! true)
        visitor (proxy [ElementVisitorBase] []
                  (visit [el]
                    (when (or (instance? ElementMinus el)
                              (instance? ElementService el)
                              (and (instance? ElementData el)
                                   (.contains (.getVars ^ElementData el) ?this))
                              (and (instance? ElementBind el)
                                   (= ?this (.getVar ^ElementBind el)))
                              (and (instance? ElementAssign el)
                                   (= ?this (.getVar ^ElementAssign el)))
                              (and (instance? ElementSubQuery el)
                                   (let [sub (.getQuery ^ElementSubQuery el)]
                                     (not (and (.contains (.getProjectVars sub)
                                                          ?this)
                                               (pre-bindable? sub))))))
                      (vreset! fine? false))))]
    (and (not (.hasLimit query))
         (not (.hasOffset query))
         (not (.hasExpr (.getProject query) ?this))
         (do (ElementWalker/walk (.getQueryPattern query) visitor)
             @fine?))))

;; SHACL-AF, section 3.1: a node is a target of a SPARQL-based target when
;; its query has a solution with ?this pre-bound to the node
(defn- target?
  "Whether the `node` of the `data` is one of the nodes that the `target`
  names.

  A SPARQL-based target is asked about the one node when its query allows
  it (see pre-bindable?). Jena runs the query in full for every node, which
  is slow when the target names many nodes."
  [^Target target ^Node node ^Graph data]
  (let [shapes (.getShapesGraph target)
        query  (when (and (= TargetType/targetExtension (.getTargetType target))
                          (G/hasOneSP shapes (.getObject target) SHACL/select))
                 (ShLib/extractSPARQLQuery shapes (.getObject target)))]
    (if (and query (pre-bindable? query))
      (with-open [qe (-> (QueryExec/graph data)
                         (.query ^Query query)
                         (.substitution (Var/alloc "this") node)
                         (.build))]
        (.hasNext (.select qe)))
      (VLib/isFocusNode target node data))))

(defn- node-report
  "The validation report of the `node` of the `data` against the `shapes`
  that it's a target of."
  ^ValidationReport [^Shapes shapes ^Graph data ^Node node]
  (let [context (ValidationContext/create shapes data)]
    (doseq [^Shape shape (.getTargetShapes shapes)
            :when (some #(target? % node data) (.getTargets shape))]
      (VLib/validateShape context data shape node))
    (.generateReport context)))

(defn validate
  "The SHACL report of `db` (or only of its `node`) against the `shapes`, as
  a map of :conforms? and :results. The shapes are anything that parse
  takes, e.g. a file or a db. The report is made in one read transaction.

  The report of a `node` has the results that the report of the whole db
  has for it. A SPARQL-based target is only asked about that node, when its
  query can be.

  Without `shapes`, the shapes graph is the one that the data names, as
  SHACL has it: the graphs that `db` names with sh:shapesGraph and those
  that they import with owl:imports. They're looked up among the named
  graphs of its Dataset, and nothing is fetched from the web.

  Each result is a map of :focus-node, :path, :value, :source-shape,
  :constraint-component, :message and :severity. Its keywords use the
  prefixes of `db`, and sh for SHACL, e.g. :sh/Violation. A path that isn't
  a single predicate is a string of SPARQL syntax."
  ([db]
   (validate db (txn/calculate-read db #(linked-shapes db)) nil))
  ([db shapes]
   (validate db shapes nil))
  ([{:keys [prefixes] :as db} shapes node]
   (let [prefixes (assoc prefixes :sh "<http://www.w3.org/ns/shacl#>")
         shapes   (parse shapes)]
     (txn/calculate-read
       db
       #(let [g (theo/jena-graph db)]
          (report->map (if (some? node)
                         (node-report shapes g (convert/node node prefixes))
                         (.validate (ShaclValidator/get) shapes g))
                       prefixes))))))

(defn by-severity
  "The results of the `report` grouped by their :severity."
  [report]
  (group-by :severity (:results report)))

(defn violations?
  "Whether the `report` has a result of :sh/Violation, rather than only
  :sh/Warning or :sh/Info."
  [report]
  (boolean (some #(= :sh/Violation (:severity %)) (:results report))))
