;Types
;predicate : (name:string, variable-params:string[])
;entry (predicate, predicate[])
;element (name:string, entries:entry[])



;collected horn clauses stored as clause name
;if there are more than one, then they are collected in list
(setq data (make-hash-table)) 

;returns element by name
(defun get-data (key)
	(gethash (read-from-string key) data))

;adds element by name
(defun put-data(key value) 
	(setf (gethash (read-from-string key) data) value))

;creates new element
(defun create-element (input) 
	(list (first (first input)) (list input)))

;adds clause with same name to group list of clauses
(defun add-entry (element input)
	(list (first element) (cons input (second element))))

;adds new element to data hash table 
(defun add-element (input) 
	(let ((element (get-data (first (first input))))) 
		(if (not element)
			(put-data(first (first input)) (create-element input))
			(put-data(first (first input)) (add-entry element input)))))

(defun name (predicate) (first predicate))

(defun all-entries (element) (second element))


(defun is-variable (x) 
	(and (stringp x) 
		(upper-case-p (char x 0))))

(defun is-value (x) 
	(or (numberp x)
		(and (stringp x) 
			(lower-case-p (char x 0)))))

(defun parameters-matches (a b) 
	(or (and (is-value  a) (is-value b) (equal a b))
		(and  (is-variable a) (is-value b))
		(and  (is-variable a) (is-variable b))
		(and (is-value a) (is-variable b)) ))

(defun matches (predicate values)
	(let ((predicate-name (first predicate))
		  (clause-name (first values))
		  (predicate-args (second predicate))
		  (clause-args (second values)))
		(and 
			(equal predicate-name clause-name)
			(equal (length predicate-args) (length clause-args))
			 (every #'parameters-matches  predicate-args  clause-args ))))


;replaces child var to new var name or value
(defun assign (child-arg parent-args parent-values)
	(cond 
		((not parent-args) nil)
		((is-value child-arg) child-arg)
		((and (is-variable child-arg) (equal child-arg (first parent-args)) (first parent-values)))
		((and (is-variable (first parent-values))) (first parent-args))
		(t (assign child-arg (rest parent-args) (rest parent-args)))))

;replaces all chils vars to new vars or values
(defun assign-all (child args entry-args)
	(list (first child) 
		(mapcar #'(lambda (child-arg)
			(assign child-arg args entry-args))  (second child))))

;returns value stored by key
(defun value-of-var (key values)
	(cond
	 	((not values) nil)
	 	((equal key (first (first values))) 
			(second (first values)))
	 	(T (value-of-var key (rest values)))))

;intersects to lists as sets
(defun collect (list1 list2)
	(remove-duplicates 
		(reduce #'(lambda (acc item1) 
			(if (find-if #'(lambda (item2) (equal item1 item2)) list2) 
				(cons item1 acc)  acc))
	 	list1 :initial-value nil) :test #'equal))

(defun collect-values (key new all)
	(cond 
		((null new) all)
		((null all) (list key new)) 
		(T (list key (collect (second all) new)))))

;check whether args variables has values, return args if that
;otherwise it returns nil
(defun refine-child-values (args) 
	(if (every #'(lambda (arg) 
		(or (and  (listp arg) (not (null (second arg))))
			(not (null arg)))) args)
	 	args nil))

;intersects the sets of values of depended predicate variables
;example args (X Y) (((X (1 2 3)) (Y ("a" "b"))) ((X (1 3)) (Y ("b"))))
;will be converted  to (((X (1 3)) (Y ("b")))	
(defun filter-child-values (args entry-args children values)
	(refine-child-values 
		(if (and (equal (length children) (length values))
			(every #'(lambda (child value) 
				(equal (length (second child)) (length value)))
			children values))
				(mapcar #'(lambda (key entry-key) 
					(if (is-variable entry-key)
						(reduce #'(lambda (acc val) 
							 (collect-values key  (value-of-var key val) acc ))
						values :initial-value nil)
						(list key (list entry-key)) ))  
					args  entry-args )
				(mapcar #'(lambda (key)  (list key nil)) args)
			)))
;returs clause values
;if entry is fact then it return args
;if entry has depended predicates it recursively calls find-values for each depended predicate
;then it calls filter-child-values

(defun get-entry-values (args values entry)
	(cond 
		((and (not (second entry )) (equal (length args) (length  values) ))
			(if (every #'parameters-matches args values )
				(mapcar #'(lambda (arg value) 
					(list arg (list value))) args values)
				(mapcar #'(lambda (arg) (list arg nil)) args)))
		((equal (length args) (length values))
			(filter-child-values args (second (first entry)) (second entry) (mapcar #'(lambda (child) 
				(find-values (assign-all  child (second (first entry))  args ))) (second entry)) ))
		(T nil)))

;adds value to data with key
(defun put-value (key value data)
	(cond 
		((null  data ) (list (list key value)))
		((equal key (first (first data))) 
			(cons (list key 
				(remove-duplicates 
					(concatenate 'list value (second (first data))) 
					:test #'equal)) 
			(rest data)))
		(T (cons (first data) (put-value key value (rest data))))))

;union the sets of variables values
;example (((X (1 2 3)) (Y ("a" "b"))) ((X (3 2 4)) (Y ( "b"))))
;will be converted to ( ( (X (1 2 3 4)) (Y ("a" "b"))))
(defun union-values (values)
	(reduce #'(lambda (data value) 
		(if (null value) data
			(reduce #'(lambda (acc val) 
				(put-value (first val) (second val) acc )) 
					value :initial-value data))) 
	 values :initial-value nil))

;returns all clauses which match predicate
(defun get-entries (predicate)
	 (remove-if #'(lambda (entry) 
		(not (matches predicate (first entry))  ))
		(all-entries (get-data (first predicate)))))

;if horn clause has no args and depended predicates
(defun simple-fact ()
	(list (list (list "true" (list "true")))))

;selects all matching to predicate clauses
;for each collected entrie runs get-entry-values
;then unions the result sets
(defun find-values (predicate)
	(let ((entries (get-entries predicate)))
		(if (and (null (second predicate)) (not (null entries))) 
			(simple-fact)
			(union-values
				(reduce #'(lambda (acc entry) 
					(let ((values 
						(get-entry-values (second predicate) (second (first entry)) entry)))
					(if values (cons values acc) acc)))  entries :initial-value nil)))))

;converts emty collected variables data such as ((X nil) (Y nil)) to nil
(defun refine (data)
	(cond
		((null data) nil)
		((null (second (first (first data) ))) nil) 
		(T (cons (first data) (refine (rest data) )))))

;same as find values without unioning matched clauses values
(defun solve (predicate)
	(refine (let ((entries (get-entries predicate)))
		(if (and (null (second predicate)) (not (null entries))) 
			(simple-fact)
			(reduce #'(lambda (acc entry) 
			(let ((values 
				 (get-entry-values 
					 (second predicate)
					(second (first entry)) entry)))
			(if values (cons values acc) acc))) entries :initial-value nil)))))

;The main input processing function is process-input which defined as
;The function interpret-file is interpreting input.txt 
(defun interpret-file (input-file) 
	(let ((input-list (read-from-string 
		(reduce (lambda (a b) (concatenate 'string  a b)) 
		(with-open-file (stream input-file)
		    (loop for line = (read-line stream nil)
		          while line
		          collect line))))))

		(reduce #'(lambda (output input) 
			(cond
				((null input) (cons (to-string input (simple-fact)) output)) 
				((null (first input)) 
					(if (stringp (first (second input)))
						(cons (to-string input (print (solve (second input)))) output) 
						(cons (to-string input (every #'(lambda (predicate) 
							(solve predicate)) (second input))) output) ))
				(T (and (add-element input) output))))
		input-list :initial-value nil )))

;converts query and its result to string
(defun to-string (list result) 
	(format nil "~{~A~%~}" 
		(list (reduce (lambda (a b) 
			(concatenate 'string a b)) 
				(list "?- " 
					(if (stringp (first list)) 
						(format nil "~{~A~}" list)
					(format nil "~{~A~}" 
						(mapcar #'(lambda (lst) 
							(format nil "~{~A~}" lst)) 
						list ))))) 
		(cond ((null   result) "no")
			((typep result 'boolean) "yes")
			((every #'(lambda (key) (is-value (first key) )) (first result)) "yes")
			(T (format nil "~{~A,~}" result))))))

;writes output-data:list to filename:string
(defun write-to-file (output-data filename)
	(with-open-file (stream filename :direction :output) 
		(format stream "~{~a~^~%~}" (reverse output-data))))
	
;start point 
(defun main ()
	(let ((output-data (interpret-file "input.txt")))
		(write-to-file output-data "output.txt")))
	
(main)