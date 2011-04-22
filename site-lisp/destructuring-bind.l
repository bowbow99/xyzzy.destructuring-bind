;;; -*- mode: lisp; package: destructuring-bind -*-
;;;
;;; destructuring-bind.l --- Common Lisp ‚Ì destructuring-bind
;;;
;;; Author:     bowbow99  <bowbow99@gmail.com>
;;; Version:    0.00.00
;;; Category:
;;; License:    MIT (see COPYING.mit)
;;; Commentary: (see README.md)
;;; ChangeLog:  (see ChangeLog)

;;; Code:


(in-package :lisp)

(export '(destructuring-bind
          &allow-other-keys
          ))

(defconstant &allow-other-keys '&allow-other-keys)

(defpackage :destructuring-bind
  (:use :lisp))

(in-package :destructuring-bind)

;; * Debug flag
(defvar *debugging* nil)

(when *debugging*
  (pushnew :debug *features*))

;;;;
;;;; * Utilities

(defmacro with-ca/dr ((car-var cdr-var) cons &body body)
  `(let ((#1=#:cons ,cons))
     (let ((,car-var (car #1#))
           (,cdr-var (cdr #1#)))
       ,@body)))
#+xyzzy
(setf (get 'with-ca/dr 'ed:lisp-indent-hook) 2)

(defmacro with-places ((&rest places) object &body body)
  `(let ((#1=#:object ,object))
     (let (,@(mapcar (lambda (place)
                       (if (consp place)
                         `(,(first place) (,(second place) #1#))
                         `(,place (,place #1#))))
               places))
       ,@body)))
#+xyzzy
(setf (get 'with-places 'ed:lisp-indent-hook) 2)

(defun variablep (x)
  (and (symbolp x) (not (constantp x))))

;; modified version of http://paste.lisp.org/display/24480
(defun proper-list-p (object)
  (if (null object) t
    (and (listp object)
         (do ((fast (cdr object) (cddr fast))
              (slow object (cdr slow)))
             ()
           (cond ((null fast) (return t))
                 ((atom fast) (return nil))
                 ((null (cdr fast)) (return t))
                 ((atom (cdr fast)) (return nil))
                 ((eql fast slow) (return nil)))))))

(defmacro !invalid-lambda-list ()
  `(error 'invalid-lambda-list :datum *lambda-list*))


(defconstant &required '&required)

;; FIXME: should be constant (using `defparameter` 'cos maybe I change my mind...)
;; NOTE: `&required` and `&environment` are actually not a lambda-list keyword
;; that can be used, but included for checking presense and/or order of them with
;; `(member x ...)`. see `parse-lambda-list`.
(defparameter +destructuring-lambda-list-keywords+
  (list &environment &whole &required &optional &rest &key &allow-other-keys &aux))

(defun %assert-list-length (list min max)
  (declare (type list list)
           (type (or integer (eql nil)) min max))
  "Check LIST is a list with expected number of elements, and return the LIST as-is."
  (unless (listp list)
    (error 'type-error :datum list :expected-type 'list))
  (unless (or (null min) (zerop min) (nthcdr (1- min) list))
    (error 'too-few-arguments :datum list))
  (unless (or (null max) (<= (list-length list) max))
    (error 'too-many-arguments :datum list))
  list)

(defun %assert-keyword-list (keyword-list allowed-keywords allow-other-keys)
  "Check whether KEYWORD-LIST is proper or not, and return it as-is."
  ;; NOTE: `&allow-othe-keys X` is always permitted
  (setq allowed-keywords (cons '&allow-other-keys allowed-keywords))
  (unless (and (proper-list-p keyword-list)
               (evenp (length keyword-list))
               (or allow-other-keys
                   (getf keyword-list :allow-other-keys)
                   (do ((list keyword-list (cddr list)))
                       ((null list) t)
                     (unless (member (car list) allowed-keywords)
                       (return nil)))))
    (error 'invalid-keyword-list :datum keyword-list))
  keyword-list)

(defparameter *state/parser-alist*
  '((&required . parse-&required)
    (&optional . gen-&optional-binding)
    (&rest     . gen-&rest-binding)
    (&body     . gen-&rest-binding)
    (&key      . gen-&key-binding)
    (&aux      . parse-&aux)
    ))

(defparameter *lambda-list* nil)

(defparameter *whole-form-placeholder* nil)
(defparameter *whole-form* nil)
(defparameter *max-length* nil)
(defparameter *min-length* nil)

(defparameter *rest-form* nil)
(defparameter *rest-form-placeholder* nil)
(defparameter *rest-var* nil)

(defparameter *keyword-arguments-p* nil)
(defparameter *known-keywords* nil)
(defparameter *allow-other-keys-p* nil)

(defmacro %ASSERT-LAMBDA-LIST (&rest tests)
  `(unless (and ,@tests)
     (error 'invalid-lambda-list :datum *lambda-list*)))

(defun parse-lambda-list (lambda-list form)
  (declare (type list lambda-list))
  (let* (;; for &whole
         (*whole-form-placeholder* nil)
         (*whole-form* nil)
         (*min-length* 0)
         (*max-length* 0)
         ;; for &rest/&key
         (*rest-var* nil)
         (*rest-form-placeholder* nil)
         (*rest-form* nil)
         (*keyword-arguments-p* nil)
         (*allow-other-keys-p* nil)
         (*known-keywords* nil)
         ;; misc
         (vars  nil)
         (forms nil)
         (tail  nil)
         (state '&required))
    (multiple-value-setq (vars forms tail lambda-list)
        (parse-&whole lambda-list form))
    (progn
      (do ((lambda-list lambda-list (cdr lambda-list)))
          ((null lambda-list))
        (if (symbolp lambda-list)
          ; lambda-list was a dotted-list
          (setq lambda-list (list nil '&rest lambda-list))
          (with-ca/dr (x rest) lambda-list
            (if (member x +destructuring-lambda-list-keywords+)
              (progn
                (unless (member x (cdr (member state +destructuring-lambda-list-keywords+)))
                  (!invalid-lambda-list))
                (case x
                  ((&optional &key &aux)
                   (setq state x))
                  ((&rest &body)
                   (unless rest (!invalid-lambda-list)) ; no &rest parameter
                   (setq state x))
                  ((&allow-other-keys)
                   (setq *allow-other-keys-p* t)
                   (unless (and (eql state '&key)
                                (or (null rest)
                                    (eql (car rest) '&aux)))
                     (!invalid-lambda-list)))
                  (t
                   (error "Should not see me"))))
              (multiple-value-bind (vars% forms% tail%)
                  (funcall (or (cdr (assoc state *state/parser-alist*))
                               (error "No parser found for state `~S'."
                                      state))
                           x tail)
                (setq vars  (append vars vars%)
                      forms (append forms forms%)
                      tail  tail%))))))
      (setq forms (subst `(%assert-list-length
                           ,*whole-form* ,*min-length* ,*max-length*)
                         *whole-form-placeholder* forms)
            forms (subst (if (not *keyword-arguments-p*)
                           *rest-form*
                           `(%assert-keyword-list
                             ,*rest-form* ',*known-keywords* ,*allow-other-keys-p*))
                         *rest-form-placeholder* forms))
      #+debug (break "keywords: ~S" *known-keywords*)
      (values vars forms))))

;; NOTE: this one has bit different interface than other parse-*.
;; - 1st arg: takes entire LAMBDA-LIST rather than one PARAMETER in issue
;; - 4th value: returns (possibly modified) LAMBDA-LIST
(defun parse-&whole (lambda-list form)
  (let ((placeholder (gensym "$WHOLE-FORM-")))
    (multiple-value-bind (whole-var lambda-list vars forms)
        (cond
         ;; No &whole
         ((not (eql (car lambda-list) '&whole))
          (values (gensym "whole-") lambda-list))
         ;; &whole VARIABLE
         ((variablep (second lambda-list))
          (values (second lambda-list) (cddr lambda-list)))
         ;; &whole (PA TT . ERN)
         ((consp (second lambda-list))
          (let ((whole-var (gensym "whole-")))
            (multiple-value-bind (vars forms)
                (parse-lambda-list (second lambda-list) whole-var)
              (values whole-var (cddr lambda-list) vars forms))))
         (t
          (!invalid-lambda-list)))
      (setf *whole-form-placeholder* placeholder
            *whole-form* form)
      (values (cons whole-var vars)
              (cons placeholder forms)
              whole-var
              lambda-list))))

(defun parse-&required (param form)
  (multiple-value-bind (vars forms)
      (cond ((consp param)     (parse-lambda-list param `(car ,form)))
            ((variablep param) (values (list param) (list `(car ,form))))
            (t (!invalid-lambda-list)))
    (incf *min-length*)
    (incf *max-length*)
    (values vars forms `(cdr ,form))))

;;; * &optional
(defun parse-&optional-parameter (param)
  (cond ((consp param)
         (let ((var     (first param))
               (default (second param))
               (sp-var  (if (cddr param)
                          (third param)
                          (gensym "supplied-p-"))))
           (unless (and (null (cdddr param)) ; too many things
                        (variablep sp-var))
             (!invalid-lambda-list))
           (values var sp-var default)))
        ((variablep param)
         (values param (gensym "supplied-p-") nil))
        (t
         (!invalid-lambda-list))))

(defun gen-&optional-binding (param form)
  (multiple-value-bind (var sp-var default-form)
      (parse-&optional-parameter param)
    (let ((sp-form    `(not (null ,form)))
          (value-form `(if ,sp-var (car ,form) ,default-form)))
      (multiple-value-bind (vars forms)
          (cond ((consp var)     (parse-lambda-list var value-form))
                ((variablep var) (values (list var) (list value-form)))
                (t (!invalid-lambda-list)))
        (incf *max-length*)
        (values (list* sp-var  vars)
                (list* sp-form forms)
                `(cdr ,form))))))

;;; * &rest
(defun %setup-rest-var/form (var form)
  (setf *max-length* nil
        *rest-var*   var
        *rest-form-placeholder* (gensym "$REST-FORM-")
        *rest-form* form))

(defun gen-&rest-binding (param form)
  (when *rest-var* (!invalid-lambda-list))
  (multiple-value-bind (rest-var vars forms)
      (cond ((consp param)
             (let ((rest-var (gensym "rest-")))
               (multiple-value-bind (vars forms)
                   (parse-lambda-list param rest-var)
                 (values rest-var vars forms))))
            ((variablep param)
             (values param (list param) (list form)))
            (t
             (!invalid-lambda-list)))
    (%setup-rest-var/form rest-var form)
    (values vars forms rest-var)))

;;; * &key
(defun %keyword (name)
  (intern (string name) :keyword))

(defun parse-&key-parameter (param)
  (macrolet ((%ASSERT-PARAMETER (&rest test-forms)
               `(unless (and ,@test-forms) (!invalid-lambda-list))))
    (if (atom param)
      ;; atomic form: VAR
      (progn
        (%ASSERT-PARAMETER (variablep param))
        (values (%keyword param) param nil (gensym "keyarg-supplied-p-")))
      ;; compound form
      (let ((key/var (first param))
            (default (second param))
            (sp-var  (if (cddr param)
                       (third param)
                       (gensym "keyarg-supplied-p-"))))
        (%ASSERT-PARAMETER (null (cdddr param))
                           (variablep sp-var))
        (if (atom key/var)
          ;; (VAR DEFAULT SP-VAR)
          (progn
            (%ASSERT-PARAMETER (variablep key/var))
            (values (%keyword key/var) key/var default sp-var))
          ;; ((KEYSYM VAR/PATTERN) DEFAULT SP-VAR)
          (let ((key (first key/var))
                (var (second key/var)))
            (%ASSERT-PARAMETER (null (cddr key/var))
                               (symbolp key)
                               (or (variablep var) (consp var)))
            (values key var default sp-var)))))))

(defun gen-&key-binding (param form)
  (multiple-value-bind (*vars *forms)
      (when (null *rest-var*)
        ;; NOTE: When &key started without &rest, use GENSYM as rest-var.
        (%setup-rest-var/form (gensym "all-keyargs-") form)
        (values (list *rest-var*)
                (list *rest-form-placeholder*)))
    (multiple-value-bind (keyword var default sp-var)
        (parse-&key-parameter param)
      (let* ((sp-var     (or sp-var (gensym "keyarg-supplied-p-")))
             (sp-form    `(get-properties ,form '(,keyword)))
             (value-form `(if ,sp-var (getf ,form ',keyword) ,default)))
        (multiple-value-bind (vars forms)
            (if (consp var)
              (let ((sublist-var (gensym "keyarg-sublist-")))
                (multiple-value-bind (vars forms)
                    (parse-lambda-list var sublist-var)
                  (values (list* sp-var  sublist-var vars)
                          (list* sp-form value-form  forms))))
              (values (list sp-var  var)
                      (list sp-form value-form)))
          (setf *keyword-arguments-p* t
                *known-keywords* (cons keyword *known-keywords*))
          (values (append *vars  vars)
                  (append *forms forms)
                  *rest-var*))))))

(defun parse-&aux (param form)
  (cond
   ((consp param)
    (with-places (first second cddr) param
      (unless (and (variablep first)
                   (null cddr))
        (!invalid-lambda-list))
      (values (list first) (list second))))
   ((variablep param)
    (values (list param) (list nil)))
   (t
    (!invalid-lambda-list))))


(defmacro lisp:destructuring-bind (lambda-list expr &body body)
  (multiple-value-bind (vars values)
      (let ((destructuring-bind::*lambda-list* lambda-list))
        (destructuring-bind::parse-lambda-list lambda-list expr))
    `(let* (,@(mapcar #'list vars values))
       ,@body)))
#+xyzzy
(setf (get 'destructuring-bind 'ed:lisp-indent-hook) 2)







#+debug
(setf *features* (delete :debug *features*))



;;; destructuring-bind.l ends here.
