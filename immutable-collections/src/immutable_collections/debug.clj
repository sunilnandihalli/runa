(ns immutable-collections.debug
  (:require [clojure.contrib.macro-utils :as m]
	    [clojure.pprint :as p]
	    [clojure.walk :as w]
	    [clojure.contrib.trace :as t]
            [clojure.contrib.lazy-seqs :as ls])
  (:import [java.io BufferedReader BufferedWriter FileReader]
           [javax.swing JFrame SwingUtilities]
           java.awt.event.WindowAdapter)
  (:use clojure.inspector))


#_(gen-class :name bitvector.debug.throwableValue
           :extends java.lang.Exception
           :state val
           :prefix "throwable-value-")

(defn wait-for
  [inspector]
  (let [blocker (promise)
        adapter (proxy [WindowAdapter] []
                  (windowClosed [_e] (deliver blocker nil)))]
    (SwingUtilities/invokeAndWait
     #(doto inspector
        (.setDefaultCloseOperation JFrame/DISPOSE_ON_CLOSE)
        (.addWindowListener adapter)))
    @blocker))

(defn dbg [val] (wait-for (clojure.inspector/inspect-tree val)) val)
  
(defmacro d [frm]
  `(let [x# ~frm]
     (wait-for (clojure.inspector/inspect-tree {:form '~frm :val x#})) x#))

#_(throwable-value "hello")    

#_(defn throw-value [v err-str]
    (throw (with-meta (Exception. err-str) {:val v})))

#_(defn hello []
    (throw-value :hello "jdfsfd"))

#_(try (hello) (catch Exception e (meta e)))
#_(see (make-array Double/TYPE 3 2))
#_(clojure.pprint/pprint
   (into-array (map (partial into-array Double/TYPE) [[1 2 3 4] [5 6]])))

(defmacro defn-memoized [name & rest]
  `(do (defn ~name ~@rest) (def ~name (with-meta (memoize ~name) (meta ~name))))) 

(defmacro defn-with-source [name & rest]
  `(do (defn ~name ~@rest)
       (def ~name (with-meta ~name
                    (assoc (meta ~name) :source '~&form)))))

(defmacro self-keyed-map [& vals]
  `(into {} (vector ~@(map (fn [x] (if (symbol? x)
                                     `(vector ~(-> x name keyword)  ~x)
                                     `(vector ~(-> (gensym "key-") name keyword) (with-meta ~x {:s-exp '~x}))))
                           vals))))  

(defn inc-or-init [x] (if x (inc x) 1))

(defn non-std-update! [tr-mp key f]
  (let [x (tr-mp key)
        fx (f x)]
    (assoc! tr-mp key fx)))

(defn non-std-into! [tr-mp1 tr-mp2]
  (let [mp2 (persistent! tr-mp2)]
    (reduce #(conj! %1 %2) tr-mp1 mp2)))


(defmacro display
  ([& forms]
     `(inspect-tree (self-keyed-map ~@forms))))
(defn ensure-sortedness [coll]
  (cond
   (sorted? coll) coll
   (map? coll) (into (sorted-map) coll)
   (coll? coll) (into (sorted-set) coll)
   :else (throw (Exception. "not a collection"))))
   

#_(self-keyed-map s z)

(defmacro fnd [& rest]
  `(with-meta (fn ~@rest) {:source '~&form}))

(defmacro ->var [first & exprs]
  (if (seq exprs) `(let [~'var ~first] (->var ~@exprs)) first))

(defmacro thrush-with-sym [[sym] first & exprs]
  `(let [~sym ~first] ~(if (seq exprs) `(thrush-with-sym [~sym] ~@exprs) sym)))

(defmacro thrush-with-sym-dbg [[sym] first & exprs]
  `(let [~sym ~first]
     (println ['~first ~sym])
     ~(if (seq exprs) `(thrush-with-sym-dbg [~sym] ~@exprs) sym)))

(defmacro nil-safe-thrush-with-sym [[sym] fst & rst]
  (if (seq rst) `(if-let [~sym ~fst] (nil-safe-thrush-with-sym [~sym] ~@rst)) fst))

(defmacro exception-safe-thrush-with-sym [[sym] fst & rst]
  `(try
     (let [~sym ~fst]
        ~(if (seq rst) `(exception-safe-thrush-with-sym [~sym] ~@rst) fst))
     (catch Exception e#
       (. *err* print
          (format "Caught exception : %s \nform : %s\n" e# (str ~fst))))))

(defmacro exception-safe-thrush-with-sym-dbg [[sym] fst & rst]
  `(try
     (let [~sym ~fst]
       (println ['~sym ~sym])
        ~(if (seq rst) `(exception-safe-thrush-with-sym [~sym] ~@rst) fst))
     (catch Exception e#
       (. *err* print
          (format "Caught exception : %s \nform : %s\n" e# (str ~fst))))))

(defmacro defmutabletype [type-name members]
  (let [proto-name (symbol (str "I" (name type-name)))
	member-setter-names (map #(symbol (str (name %) "!")) members)
	member-setter-prototypes (map (fn [setter-name]
					`(~setter-name [this# newval#]))
				      member-setter-names)
	member-setter-fns (map (fn [setter-name member-name]
				 `(~setter-name [this# newval#] (set! ~member-name newval#)))
			       member-setter-names members)
	member-getter-prototypes (map (fn [member-name] `(~member-name [this#])) members)
	member-getter-fns (map (fn [member-name]
				 `(~member-name [this#] ~member-name))
			       members)
	annotated-members (vec (map (fn [name]
				      (with-meta name (assoc (meta name) :volatile-mutable true)))
				    members))]
    `(do
       (defprotocol ~proto-name
	 ~@member-getter-prototypes
	 ~@member-setter-prototypes)
       (deftype ~type-name ~annotated-members
	 ~proto-name
	 ~@member-getter-fns
	 ~@member-setter-fns))))

(defmacro timed [f]
  `(fn [& args#] (let [f# ~f
		       ret# (time (apply f# args#))]
		   (println '~f) ret#)))

(defn reoder-map [mp new-order])
  
(defmacro save-local-variables [& [prefix]]
  (let [new-prefixed-defs (map (fn [x]
                                 (let [new-name (symbol (str prefix (name x)))]
                                   `(do
                                      (println "saving " '~x " as " '~new-name)
                                      (def ~new-name ~x)))) (keys &env))]
    `(do ~@new-prefixed-defs)))

(defmacro def-curry-fn [name args & body]
  {:pre [(not-any? #{'&} args)]}
  (if (empty? args)
    `(defn ~name ~args ~@body)
    (let [rec-funcs (reduce (fn [l v]
			      `(letfn [(helper#
					 ([] helper#)
					 ([x#] (let [~v x#] ~l))
					 ([x# & rest#] (let [~v x#]
							 (apply (helper# x#) rest#))))]
				 helper#))
			    `(do ~@body) (reverse args))]
      `(defn ~name [& args#]
	 (let [helper# ~rec-funcs]
	   (apply helper# args#))))))

(defmacro values [& args]
  (let [f (fn [x] [`'~x x])
	keyworded-args (mapcat f args)]
    `(hash-map ~@keyworded-args)))

#_(let [x 10
	y 20]
    (values x y (* x y) (+ x y)))
      
(defn vecify [& stuff]
  (loop [v [] s (seq stuff) splice false]
    (if s
      (let [f (first s)]
	(if (coll? f)
	  (if splice
	    (recur (into v f) (next s) false)
	    (recur (conj v f) (next s) false))
	  (if (= f :splice)
	    (recur v (next s) true)
	    (recur (conj v f) (next s) false))))
      v)))

(defmacro defmulti-m [multi-fn-name dispatch-fn ]
  `(let [dfn# ~dispatch-fn
	 dvalmap# (atom {})]
     (defn ~(symbol (str "add-method-to-" (name multi-fn-name)))
       [key# method-fn#]
       (swap! dvalmap# assoc key# method-fn#))
     (defn ~multi-fn-name [& args#]
       (let [ks# (keys @dvalmap#)
	     k# (or (some #(when (dfn# % args#) %) ks#) :default)
	     func-to-call# (@dvalmap# k#)]
	 (if func-to-call#
	   (try (apply func-to-call# args#)
		(catch Exception _#
		  (throw (Exception. (str "application of " ~(name multi-fn-name)
					  " method corresponding to key "
					  k# " with args " args#
					  "failed with an exception...")))))  
	   (throw (Exception.
		   (str "could not find an approriate method for the args"
			args#))))))))
	 
(defmacro defmethod-m [multi-fn-name dispatch-val args & body]
  `(~(symbol (str "add-method-to-" (name multi-fn-name)))
    ~dispatch-val (fn ~args ~@body)))
	 
#_(defmulti-m hello #(even? (apply - %1 %2)))
#_(defmethod-m hello 3 [& d] :hello)
#_(defmethod-m hello 4 [& d] :heeeeellllllooooooooooo)
#_(hello 6 7 8 )

(defmacro deep-aget
  ([hint array idx]
     `(aget ~(vary-meta array assoc :tag hint) ~idx))
  ([hint array idx & idxs]
     `(let [a# (aget ~(vary-meta array assoc :tag 'objects) ~idx)]
	(deep-aget ~hint a# ~@idxs))))

(defmacro deep-aset [hint array & idxsv]
  (let [hints '{doubles double ints int}
	;; writing a comprehensive map is left as an exercise to the reader
	[v idx & sxdi] (reverse idxsv)
	idxs (reverse sxdi)
	v (if-let [h (hints hint)] (list h v) v)
	nested-array (if (seq idxs)
		       `(deep-aget ~'objects ~array ~@idxs)
		       array)
	a-sym (with-meta (gensym "a") {:tag hint})]
    `(let [~a-sym ~nested-array]
                (aset ~a-sym ~idx ~v))))

(defn array? [x] (-> x class .isArray))
(defn see [x] (if (array? x) (map see x) x))

(defmacro display-local-bindings []
  `(do ~@(map (fn [x#] (list p/pprint  [`'~x# x#])) (keys &env))))    

(defmacro display-local-bindings []
  (let [generate-code-to-print-symbol (fn [x]
					`(p/pprint ['~x ~x]))
	all-local-symbols (keys &env)
	list-of-all-print-statements (map generate-code-to-print-symbol all-local-symbols)]
    `(do ~@list-of-all-print-statements)))

(defn all-visible-fns []
  (->> *ns* ns-refers (map first) 
       (filter #(let [v (ns-resolve *ns* %)]
		  (and (bound? v) (->> v meta :macro not) (fn? @v))))))

(defn all-fns []
  (->> *ns* ns-refers (map first) 
       (filter #(let [v (ns-resolve *ns* %)]
		  (and (bound? v) (->> v meta :macro not) (fn? @v))))))

(defn all-core-fns []
  (all-fns 'clojure.core))

(defmacro extreme-debug [& body]
  `(t/dotrace ~(all-visible-fns) (do ~@body)))

(defmacro debug [& body]
  `(t/dotrace ~(all-fns) (do ~@body)))
#_(all-visible-fns)

#_(all-fns)

(defn print-and-return
  ([x] (clojure.pprint/pprint x) x)
  ([flag x] (clojure.pprint/pprint [flag x]) x))

(defmacro print-and-return-macro
  ([x]
     `(let [x# ~x]
	(clojure.pprint/pprint x#) x#))
  ([flag x]
     `(let [flag# ~flag
	   x# ~x]
	(clojure.pprint/pprint flag#)
	(clojure.pprint/pprint x#)
	x#)))

#_(defmacro for-indexed [bindings & body]
    "does not support the :when clause yet..."
    (let [indexed-bindings (->> bindings
				(partition 2)
				(map (fn [pair]
				       `(map vector (range) ~(second pair)))))]))

(defn add-symbol-to-lists [coll sym]
  (clojure.walk/walk (fn [x]
		       (cond
			(and (list? x) ('#{->> -> quote} (first x))) (sym x) 
			(special-symbol? x) x
			(coll? x) (list sym (add-symbol-to-lists x sym))

			true (list sym x)))
		     identity			     
		     coll))

(defmacro gp-error [message]
  `(do
     (display-local-bindings)
     (println ~message)
     (println ~(meta message))
     (println *file*)
     (println '~&form)
     (println ~(meta &form))
     (throw (Exception. ~message))))



(let [level (atom 0)]
  (defmacro inc-level [] (swap! level inc) nil)
  (defmacro dec-level [] (swap! level dec) nil)
  (defmacro with-separator [& body]
    `(do
       (inc-level)
       (println)
       (println ~(str "----------------------------start-" @level "-----------------------"))
       (let [x# (do ~@body)]
	 (println  ~(str "------------------------------end-" @level "-----------------------"))
	 (dec-level)
	 x#))))

(let [*stack-of-local-binding-maps* (atom '())]
  (defmacro pop-environment [] (swap! *stack-of-local-binding-maps* pop) nil)
  (defmacro push-environment [] (swap! *stack-of-local-binding-maps* conj &env) nil)
  (defmacro dnlbh [& body]
    (let [new-locals (->> (clojure.set/difference (set &env)
						  (set (first @*stack-of-local-binding-maps*)))
			  (into {}) keys)
	  print-statements (map (fn [x] `(println ['~x ~x])) new-locals)]
      `(with-separator
	 ~@print-statements
	 (push-environment)
	 (let [x# (do ~@body)]
	   (dorun (map clojure.pprint/pprint ['~&form " returned " x#]))
	   (pop-environment)
	   x#)))))


#_(let [-nesting-level- 0]
    (defmacro hello [& body]
      `(do
	 (let [~'-nesting-level- (inc ~-nesting-level-)]
	   (println ~-nesting-level-)
	   ~@(cond
	      (empty? body) body
	      (> (count body) 1) (map (fn [x] `(hello x)) body)
	      (= (count body) 1) `(~(first body) ~@(map (fn [x] `(hello x)) (rest body)))) 
	   (println "finished " ~-nesting-level-)))))
    
(defn add-hello [coll]
  (clojure.walk/walk (fn [x]
		       (if (coll? x)
			 (add-hello x)
			 (list :h x)))
		     (fn [x] (let [l (list :h x)]
			       (if (list? x)
				 l (into (empty x) (list :h x))))) coll))

(defn add-hello [coll]
  (clojure.walk/walk #(if (coll? %)
			(add-hello %) %)
		     #(into (empty %) (list :h %)) coll))

#_(add-hello '(let [x 10] (let [y 2] (+ x y))))
#_'((:h let) [(:h x) (:h 10)] ((:h let) [(:h y) (:h 2)] ((:h +) (:h x) (:h y))))
#_'(:h ((:h let) (:h [(:h x) (:h 10)]) (:h ((:h let) (:h [(:h y) (:h 2)]) (:h ((:h +) (:h x) (:h y)))))))
#_'(:h (let (:h [x 10]) (:h (let (:h [y 2]) (:h (+ x y))))))
#_'(:h (let [:h [x 10]] (:h (let [:h [y 2]] (:h (+ x y))))))



(defmacro dnlb [& body]
  "does not work .... :("
  (add-symbol-to-lists body 'dnlbh))
  
(defn seqize [coll]
  (clojure.walk/walk (fn [x]
		       (if (coll? x)
			 (seqize (seq x)) x))
		     seq (seq coll)))

(defn collect-syms [sexp]
  (clojure.walk/walk (fn [x]
		       (if (coll? x)
			 (collect-syms (seq x))
			 (when (and (not (special-symbol? x))
				    (symbol? x))
			   #{x})))
		     (fn [x]
		       (apply concat x))
		     sexp))
		     
(defn is-symbol-bound [])
#_(def sexp '#{ a #{b #{c :d} e} [x y] (u v) {:h 10 20 :e :z tt } #{f g}})
#_(def sexp '{:a s})
#_(collect-syms sexp)

(defmacro eval-with-local-vars [vars sexp]
  (let [quoted-vars (vec (map #(list 'quote %) vars))]
    `(let [varvals# (vec (interleave ~quoted-vars ~vars))]
       (eval (list 'clojure.core/let varvals# ~sexp)))))

(defmacro eval-with-local-bindings1 [sexp]
  `(eval-with-local-vars ~(apply vector (keys &env)) ~sexp))

(defmacro eval-with-local-bindings [sexp]
  `(eval `(let ~~(->> (keys &env)
		      (mapcat (fn [x#] [`'~x# x#]))
		      (apply vector))
	    ~~sexp)))

(defmacro letd [bindings & body]
  (let [lbinds (take-nth 2 bindings)
	rbinds (take-nth 2 (drop 1 bindings))
	lsyms (repeatedly (count lbinds) gensym)]
    (reduce (fn [val [lsym lbind rbind]] `(with-separator
					    (let [~lsym ~rbind
						  ~lbind ~lsym]
					      (p/pprint ['~lbind
							 '~rbind
							 ~lsym])
					      ~val)))
	    `(do ~@body)
	    (reverse (map vector lsyms lbinds rbinds)))))



(defmacro ->d [ & args]  
  `(with-separator (-> ~@(interpose 'print-and-return args) print-and-return)))

(defmacro ->dd [ & args]
  `(with-separator (-> ~@(interleave args
				     (map (fn [x] `((fn [k#] (print-and-return ~x k#))))
					  args)))))

(defmacro ->>d [ & args]
  `(with-separator (->> ~@(interpose 'print-and-return args) print-and-return)))

(defmacro ->>dd [& args]
  `(with-separator (->> ~@(interleave args
				      (map (fn [x] (list 'print-and-return x)) args)))))


(defn scaffold [iface]
  "this code is from Christophe Grand .. but very usefull.. so I chose to include.."
  (doseq [[iface methods] (->> iface .getMethods
			       (map #(vector (.getName (.getDeclaringClass %))
					     (symbol (.getName %))
					     (count (.getParameterTypes %))))
			       (group-by first))]
    (println (str "  " iface))
    (doseq [[_ name argcount] methods]
      (println
       (str "    "
	    (list name (into ['this] (take argcount (repeatedly gensym)))))))))


                
  