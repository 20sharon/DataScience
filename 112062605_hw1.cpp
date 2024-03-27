#include <iostream>
#include <fstream>
#include <vector> // vector
#include <sstream> // stringstream
#include <algorithm> // sort
#include <unordered_set> // unordered_set
#include <unordered_map> // unordered_map
#include <string> // string
#include <iomanip> // setprecision
using namespace std;

struct FPNode;
struct FPNode_hash{
    std::size_t operator()(const FPNode *a) const;
};
struct FPNode_equal {
    bool operator()(const FPNode *node1, const FPNode *node2) const;
};
struct FPNode{
    bool visited;
    int freq; 
    int count_freq;
    int subfptree_item;
    short int num; // -1 means root

    FPNode* parent; 
    unordered_set<FPNode*, FPNode_hash, FPNode_equal> child;
    FPNode* next_same_item;
    
    FPNode(short int a):visited(false), num(a){} // only for comparing
    FPNode(int item, short int a):visited(false), subfptree_item(item), num(a){} // only for comparing
    FPNode(int f = 0, int cf = 0, int si = -1, short int n = -1, FPNode* p = nullptr){
        visited = false;
        freq = f;
        count_freq = cf;
        subfptree_item = si;
        num = n;
        parent = p;
        child = unordered_set<FPNode*, FPNode_hash, FPNode_equal>();
        next_same_item = nullptr;

    }
    bool operator==(const FPNode &other) const {
        return (num == other.num);
    }
};

std::size_t FPNode_hash::operator()(const FPNode *a) const{
    return a->num;
}
bool FPNode_equal::operator()(const FPNode *node1, const FPNode *node2) const {
        return node1->num == node2->num;
}

struct HeaderTable_nextpointer{
    int item;
    FPNode* start;
    FPNode* end;
};


//test
void DFS(FPNode* node)
{
    // Mark the current node as visited and
    // print it
    node->visited = true;
    cout <<"("<< node->num << ","<<node->freq<<","<<node->count_freq<<")";
 
    // Recur for all the vertices adjacent
    // to this vertex
    for (auto& elem: node->child){
        if (!elem->visited)
            DFS(elem);
    }
    node->visited = false;
}
//testend

void DFS_subfptree(FPNode* node, FPNode* new_node, int i, vector<FPNode*> &headertable_list_i ) // assume node's subfptree_item is i, and 
{
    if(new_node->num == i){ // add node(i) to header table.
        headertable_list_i.push_back(new_node);
        return;
    }
    for (auto& elem: node->child){
        if(elem->subfptree_item == i ){ // found the node with subfptree_item==i in child
            FPNode* addnode = new FPNode(elem->freq, elem->count_freq, elem->subfptree_item, elem->num, new_node); // have point to the new parent.
            new_node->child.insert(addnode); // add addnode into unordered_set, and point parent to addnode
            DFS_subfptree(elem, addnode, i, headertable_list_i);
        }
    }
}


void find_PowerSet(unordered_map<string, int> &freq_pattern, int item_num, int item_node_freq, vector<short int> pattern, vector<short int> &store, int n){
    if(n==0){ // if n==0 and store.size()!=0. // single leaf addinto freq_pattern write in another place.
        if(!store.size()){
            return;
        }
        // finally, add item_i into store, and add (string, freq) into freq_pattern

        store.push_back(item_num);
        string store_str;
        auto item_vec = store.begin();
        while(item_vec != store.end()){ // change vector to string
            store_str = store_str + to_string(*item_vec) + ",";
            ++item_vec;
        }
        store_str.pop_back();
        auto search = freq_pattern.find(store_str);
        if(search == freq_pattern.end()){ // not find pattern in freq_pattern
            freq_pattern[store_str] = item_node_freq;
        }else{ // find pattern in freq_pattern
            (search)->second += item_node_freq;
        }
        store.pop_back();
        return;
    }
    
    store.push_back(pattern[n-1]);
    find_PowerSet(freq_pattern, item_num, item_node_freq, pattern, store, n-1);
    store.pop_back();
    find_PowerSet(freq_pattern, item_num, item_node_freq, pattern, store, n-1);
}

class FPGrowth{
private:
    float min_support = -1.0;
    float min_support_int;
    vector<vector<short int> >* DB;
    int HT_sort_size = -1;
    vector<HeaderTable_nextpointer> HT_FPNode; //(HT_sort_size);
    unordered_map<string, int> freq_pattern;
public:
    FPGrowth(float min_support_para, vector<vector<short int> >* db){
        min_support = min_support_para;
        DB = db;
    }

    
    static bool cmp_HT_sort(const pair<short int, int> &a, const pair<short int, int> &b){
        return (a.second > b.second);
    }

    vector<pair<short int, int>> Build_HeaderTable(void){ // build a header table and arrange DB
        
        vector<short int> sortDBeachrow(1005, 0); // init all zero.
        vector<pair<short int, int>> HT_sort;
        min_support_int = min_support * (*DB).size();

        for(int i=0;i<(*DB).size();i++){
            for(int j=0;j<(*DB)[i].size();j++){
                sortDBeachrow[(*DB)[i][j]]++;
            }
        }
        for( int i = 0; i < sortDBeachrow.size(); i++){
            if( sortDBeachrow[ i ] >= min_support){ // sort (item, freq) in HT_sort
                HT_sort.push_back(make_pair(i, sortDBeachrow[ i ]));
            }else if(sortDBeachrow[ i ]){ // sortDBeachrow[ i ]!=0
                sortDBeachrow[ i ] = 0;
            }
        }
        
        // sort headertable by the freq in descending.
        sort(HT_sort.begin(), HT_sort.end(), cmp_HT_sort);
        // scan DB to exclude mom-freq item and sort items by their freq in descending.
        for(int i=0;i<(*DB).size();i++){
            sort((*DB)[i].begin(), (*DB)[i].end(), [this, &sortDBeachrow](short int a, short int b){return (sortDBeachrow[a] > sortDBeachrow[b]);});
        }
        HT_sort_size = HT_sort.size();
        return HT_sort;
    }

    FPNode* Build_FPTree(const vector<pair<short int, int> > &HT_sort){
        vector<int> exist(1005, 0); // to check the freq in the fptree >= min_support
        HT_FPNode.resize(HT_sort.size());
        for(int i=0;i<HT_sort.size();i++){
            HT_FPNode[i].item = HT_sort[i].first;
            HT_FPNode[i].start = nullptr;
            HT_FPNode[i].end = nullptr;
        }
        FPNode *root = new FPNode();
        root->subfptree_item = 1009; // random number
        
        int count_subfptree_item = 1100;
        for(int i=0;i<(*DB).size();i++){
            FPNode *parent = root;

            for(int j=0;j<(*DB)[i].size();j++){
                // since in FPNode_equal::operator(), node1->num == node2->num || node1->subfptree_item == node2->subfptree_item.
                // but when creating FPtree, all subfptree of each node are different. so, using find is OK.
                auto search = parent->child.find(new FPNode((*DB)[i][j])); // find if the item in the parent's child

                if(search == parent->child.end()){ // not found node(*DB[i][j]) in child
                    count_subfptree_item += 1;
                    FPNode *addnode = new FPNode(1, 0, count_subfptree_item, (*DB)[i][j], parent); // point addnode to parent
                    parent->child.insert(addnode); // add addnode into unordered_set, and point parent to addnode
                    parent = addnode; // update parent
                    if(HT_FPNode[(*DB)[i][j]].start == nullptr){ // HT_FPNode[(*DB[i][j])].end is also nullptr.
                        HT_FPNode[(*DB)[i][j]].start = addnode; // change headertable's link
                        HT_FPNode[(*DB)[i][j]].end = addnode; // change headertable's link
                    }else{
                        HT_FPNode[(*DB)[i][j]].end -> next_same_item = addnode; // change headertable's link
                        HT_FPNode[(*DB)[i][j]].end = HT_FPNode[(*DB)[i][j]].end -> next_same_item; // change headertable's link
                    }
                    
                }else{ // found node(*DB[i][j]) in child
                    parent = *search; // update parent
                    parent->freq += 1;
                }
            }
        }
        return root;
    }

    void Build_Subfptree(int i, FPNode* root){ // construct the subtree with leave item(i)
        FPNode* root_i = new FPNode();
        FPNode* node_i = HT_FPNode[i].start;
        unordered_map<int, int> subfptree_total_freq; // (item_num, freq)
        while(node_i != nullptr){ // all element(containing node(i), not containing root) in the subtree with leave item(i) 's subfptree_item = i, write in origin tree.
            // consider node_i with leave item(i).
            FPNode *highest_parent_i = node_i;
            int node_i_freq = node_i->freq;
            while(highest_parent_i->parent != nullptr){ // find the highest parent of node_i's (not including root).
                // update unordered_map<int, int> subfptree_total_freq; // (item_num, freq)
                auto search = subfptree_total_freq.find(highest_parent_i->num);
                if(search != subfptree_total_freq.end()){ // have already in map
                    search->second += node_i_freq;
                }else{ // not in map
                    subfptree_total_freq[highest_parent_i->num] = node_i_freq;
                }
                highest_parent_i->subfptree_item = i; 
                highest_parent_i = highest_parent_i->parent;
            } // highest_parent_i is the highest parent of node_i's.
            
            node_i = node_i->next_same_item;
        }
        // Now, know which node in the total fptree is with leave item(i). By subfptree_item.
        // construct the subtree with leave item(i) from root.
        vector<FPNode*> headertable_list_i;
        DFS_subfptree(root, root_i, i, headertable_list_i);
        // update count_freq of each node, and unordered_map<int, int> subfptree_total_freq; // (item_num, freq).
        for(auto iter = headertable_list_i.begin();iter != headertable_list_i.end();iter++){ 
            FPNode* sub_node_i = *iter;
            // consider node_i with leave item(i).
            int sub_node_i_freq = sub_node_i->freq;
            FPNode *sub_highest_parent_i = sub_node_i;
            while(sub_highest_parent_i->parent != nullptr){ // find the highest parent of node_i's.
                // updata count_freq.
                sub_highest_parent_i->count_freq += sub_node_i_freq; 
                sub_highest_parent_i = sub_highest_parent_i->parent;
            } // highest_parent_i is the highest parent of node_i's.
            
 
        }

        // find low_freq node.

        // store freq_pattern without delete
        // unordered_map<string, int> freq_pattern; // (pattern, freq)
        for(auto iter = headertable_list_i.begin();iter != headertable_list_i.end();++iter){ // consider each leaf.
            vector<short int> pattern;
            
            FPNode* parent_node = (*iter)->parent; // not start from item i.
            if(parent_node->num == -1){
                continue;
            }

            while(parent_node->num != -1){ // while the node is not root
                if(subfptree_total_freq[parent_node->num] >= min_support_int){
                    pattern.push_back(parent_node->num);
                }

                parent_node = parent_node->parent;
            }
            if(pattern.size()){ // pattern.size() != 0
                vector<short int> store;
                find_PowerSet(freq_pattern, i, (*iter)->freq, pattern, store, pattern.size());
            }
            
            // // Now, done: pattern(not containing item_i).
        }
        // single leaf addinto freq_pattern write in here.
        freq_pattern[to_string(i)] = subfptree_total_freq[i];
        //
                
    }

    unordered_map<string, int>  get_freq_pattern(void){
        return freq_pattern;
    }
    
    float get_min_support_int(){
        return min_support_int;
    }
};

int main(int argc, char* argv[])
{
    float min_support = stof(argv[1]);
    // store input into DB
    vector<vector<short int> > DB;
    ifstream inputfile(argv[2]);
    if (inputfile.is_open()){
        string line;
        unsigned short int i = 0;
        while(getline(inputfile, line)){
            vector<short int> tx_one;
            string subline;
            stringstream ss(line);
            while(getline(ss, subline, ',')){ //(ss.good()){
                tx_one.push_back(stoi(subline));
            }
            DB.push_back(tx_one);
        }
        inputfile.close();
    }
    // end: read file
    FPGrowth *fpgrowth = new FPGrowth(min_support, &DB);

    
    vector<pair<short int, int>> ht_sort = fpgrowth->Build_HeaderTable();

    FPNode* root = fpgrowth->Build_FPTree(ht_sort);
    
    for(int i=ht_sort.size()-1;i>=0;i--){
        fpgrowth->Build_Subfptree(ht_sort[i].first, root); // need become for loop.
    }
    // write in output file
    ofstream outputfile(argv[3]);
    unordered_map<string, int> freq_pattern = fpgrowth->get_freq_pattern();
    float min_support_int = fpgrowth->get_min_support_int();
    for (auto& elem: freq_pattern){
        if(elem.second<min_support_int){
            continue;
        }
        outputfile <<elem.first <<":";
        outputfile <<fixed<< setprecision(4) <<((float)elem.second)/((float)DB.size())<<endl;
    }

    return 0;
}