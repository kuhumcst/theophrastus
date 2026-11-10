(ns dk.cst.theophrastus.origin-test
  "The origins of an entity's values, read and built in Clojure and
  ClojureScript."
  (:require [clojure.test :refer [deftest is]]
            [dk.cst.theophrastus.origin :as origin]))

(def rex
  "An entity whose values come from two graphs and inference."
  {:rdf/about :ex/rex
   :rdf/type  #{:ex/Dog :ex/Animal}
   :ex/name   "Rex"
   :ex/collar {:rdf/about '_collar :ex/colour "red"}
   :ex/age    3})

(def rex-origins
  "The origin of each value of rex, by property and value."
  {[:rdf/type :ex/Dog]    :ex/g
   [:rdf/type :ex/Animal] :inferred
   [:ex/name "Rex"]       #{:ex/g :ex/h}
   [:ex/collar '_collar]  :ex/g
   [:ex/age 3]            :ex/h})

(defn rex-origin
  "The origin of the value `v` of the property `p` of rex."
  [p v]
  (get rex-origins [p v]))

(deftest building
  (is (= {:rdf/type  {:ex/Dog :ex/g :ex/Animal :inferred}
          :ex/name   #{:ex/g :ex/h}
          :ex/collar :ex/g
          :ex/age    :ex/h}
         (origin/origins rex rex-origin))
      "one origin when every value has it, and a map when they differ")
  (is (= {:rdf/type {:ex/Animal :inferred}
          :ex/name  #{:ex/g :ex/h}
          :ex/age   :ex/h}
         (origin/origins rex rex-origin :ex/g))
      "no entry for a value of the default origin")
  (is (= {:rdf/type {:ex/Dog :ex/g}}
         (origin/origins rex #(when (= :ex/Dog %2) :ex/g)))
      "no entry for a value without an origin")
  (is (= {:ex/hyponym :inferred}
         (origin/origins {:ex/hyponym [:ex/a :ex/b]} (constantly :inferred)))
      "the values of a vector"))

(deftest reading
  (let [m {:origins        (origin/origins rex rex-origin :ex/g)
           :default-origin :ex/g}]
    (is (= :inferred (origin/origin m :rdf/type :ex/Animal)))
    (is (= :ex/g (origin/origin m :rdf/type :ex/Dog)) "the default")
    (is (= #{:ex/g :ex/h} (origin/origin m :ex/name "Rex")))
    (is (= :ex/g (origin/origin m :ex/collar (:ex/collar rex)))
        "a blank node by its map")
    (is (= :ex/g (origin/origin m :ex/collar '_collar)) "or by its symbol")
    (is (nil? (origin/origin {:origins {}} :ex/name "Rex"))
        "nil without a default")))
