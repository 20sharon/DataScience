## Code
 - run_model_output_inputdata_csv.ipynb: generate 0109tryinputmodelC.csv file which contains total data set (c1, c2, and c3). I add some code from run_model.ipynb provided by Han-Jay Shu. 
 - run_model_output_nnroccurve_csv.ipynb: generate nn_for_roc.csv file to print ROC curve for NN model. I add some code from run_model.ipynb provided by Han-Jay Shu. 
 - c1_c2.ipynb: generate 0108tryc3_stayid.csv file which contains only c1 set and c2 set, without c3 set. And generate Tableone of before_weaning_hr = 0 and before_weaning_hr = 23. 
 - 4_model_using_C_input_with_0108newdata.ipynb: train four models (Decision Tree, Random Forest, SVM, XGBoost) with the total data set containing c1, c2, and c3. And can print accuracy, feature importance for the four models, and ROC curve for the five models. 
 - 4_model_using_C_input_only_contain_c1c2.ipynb: train four models (Decision Tree, Random Forest, SVM, XGBoost) with the total data set containing c1, c2, without c3. And can print accuracy, feature importance, and ROC curve for the four models. 

## CSV
 - ground_truth: containing the ground truth for each stay_id
 - 0109tryinputmodelC: containing total data set (c1, c2, and c3) with the features using in NN model
 - 0108tryc3_stayid: containing only c1 set and c2 set
 - train_data_id, val_data_id, test_data_id: stay_id for train set, validation set, test set, respectively
 - {model}_for_roc: using for draw roc curve with data c1, c2, and c3, where {model} could be dt, rf, svm, xgb, nn
 - {model}c1c2_for_roc: using for draw roc curve with data c1 and c2, where {model} could be dt, rf, svm, xgb




 
