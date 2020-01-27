#include <iostream>
#include <string>
#include <sstream>
#include <list>
#include <cmath>
#include <vector>
#include <stack>
#include <fstream>
#include <set>
#include <algorithm>
#include <time.h>
#include <sys/time.h>
#include <random>

#define OPERAND 0
#define OPERATOR 1
#define H 0
#define V 1

using namespace std;

// Files for read and write
FILE *block_file, *net_file, *terminal_file;
FILE *solution_file;

// struct for net, terminal, block, and expression list
struct net {
    int degree;
    list<int> block_list;
    list<int> terminal_list;
};

struct terminal {
    int pin_index;
    int x_coordinate, y_coordinate;
};

struct BlockInfo {
    int block_index;
    int width, height;
    int area;
    int x_coordinate, y_coordinate;
    vector<pair<int, int>> dims;
    int rotate;  // 0 indicates non-rotate, and 1 indicates rotate
};

struct tree_node {
    int node_type;
    int value;
    tree_node(int _node_type, int _value) : node_type(_node_type), value(_value) {}
};

struct newPair {
    int width;
    int height;
    int* rotate_array;
    newPair(int _width, int _height, int* _rotate) : width(_width), height(_height), rotate_array(_rotate) {}
};

struct Tile {
    string index;
    vector<newPair> dims;
    Tile(string str, vector<newPair> d) : index(str), dims(d) {}
};

// floorplanning region
float dead_ratio = 0.15;
int floorplanning_outline; // according to dead ration to calculate the outline of the floorplan region

// block information
int block_num;
int terminal_num;
int total_area = 0; // sum of the block's area
BlockInfo* blocks;

// netlist information
int net_num, pin_num;
net* net_array;

// terminal information
terminal* terminal_array;

// final answer for wire length
int wire_length;

// cost function
unsigned int cost;

// reverse operation_1
int invert_index = 0;

// creating best solution of the floorplan variables
int best_width = 1000000;
int best_height = 10000000;

// Helper structure used in function cal_final_wirelength
// Uses STL <set>
struct ConstructBlock {
    int width, height;
    set<int> block_ids;
    
    ConstructBlock() {
        width = 0;
        height = 0;
        block_ids = set<int>();
    }

    ConstructBlock(const int &idx) {
        width = (blocks[idx].rotate) ? blocks[idx].height : blocks[idx].width;
        height = (blocks[idx].rotate) ? blocks[idx].width : blocks[idx].height;
        block_ids.insert(idx);
    }

    ConstructBlock &operator=(const ConstructBlock &other) {
        width = other.width;
        height = other.height;
        block_ids = other.block_ids;

        return *this;
    }
};
    
double get_wall_time() {
    struct timeval time;
    if (gettimeofday(&time,NULL)) return 0;
    
    return (double)time.tv_sec + (double)time.tv_usec * .000001;
}

double get_cpu_time() {
    return (double)clock() / CLOCKS_PER_SEC;
}

// read file from .blocks, .nets, .pl
void readBlock(FILE* file) {
    fscanf(file, "NumHardRectilinearBlocks : %d\n", &block_num);
    fscanf(file, "NumTerminals : %d\n\n", &terminal_num);
    
    int count = block_num;
    int i = 0;
    
    blocks = new BlockInfo[block_num]();
    
    while(count--) {
        int a, b, c, d, e, f; //ignore parameter
            
        fscanf(file, "sb%d hardrectilinear 4 (%d, %d) (%d, %d) (%d, %d) (%d, %d)\n", &blocks[i].block_index, &a, &b, &c, &d, &blocks[i].width, &blocks[i].height, &e, &f);
        
        blocks[i].rotate = 0;
        blocks[i].area = (blocks[i].width) * (blocks[i].height);
        total_area += blocks[i++].area;
    }
        
    return;
}

// reading .nets file
void readNets(FILE* file) {
    fscanf(file, "NumNets : %d\n", &net_num);
    fscanf(file, "NumPins : %d\n", &pin_num);
    
    net_array = new net[net_num]();
    
    for (int i = 0; i < net_num; i++) {
        int net_degree;
        fscanf(file, "NetDegree : %d", &net_degree);
        net_array[i].degree = net_degree;
        
        while(net_degree--) {
            int tmp_id;
            char tmp_char[10];
            fscanf(file, "%s\n", tmp_char);
            if(tmp_char[0] == 's') {                             // it's a block, so we push it into block_list
                string tmp_string(tmp_char);
                for(char &c : tmp_string) if(!isdigit(c)) c=' ';
                stringstream ss(tmp_string);
                ss >> tmp_id;
                net_array[i].block_list.push_back(tmp_id);
            } else {                                             // it's a terminal, so we push it into terminal_list
                string tmp_string(tmp_char);
                for(char &c : tmp_string) if(!isdigit(c)) c=' ';
                stringstream ss(tmp_string);
                ss >> tmp_id;
                net_array[i].terminal_list.push_back(tmp_id);
            }
        }
    }
}

void readTerminal(FILE* file) {
    terminal_array = new terminal[terminal_num]();
    for(int i = 0; i < terminal_num; ++i) {
        fscanf(file, "p%d %d %d\n", &terminal_array[i].pin_index, &terminal_array[i].x_coordinate, &terminal_array[i].y_coordinate);
    }
}
    
// create better poslish expression, this one is better since it will record all posible combination of the nodes(except leaves)
vector<Tile *> createNPE(vector<tree_node> expression) {
    vector<Tile *> npeElems;
    unsigned long int expr_length = expression.size();
    
    for (int index = 0; index < expr_length; index++) {
                
        if (expression[index].node_type == OPERAND) {
            vector<newPair> dims_tmp;
            int* tmp1 = new int[block_num];
            for (int i = 0; i < block_num; i++) tmp1[i] = -1;
            tmp1[expression[index].value] = 0;
            dims_tmp.push_back(newPair(blocks[expression[index].value].width, blocks[expression[index].value].height, tmp1));
            
            if (blocks[expression[index].value].width != blocks[expression[index].value].height) {
                int* tmp2 = new int[block_num];
                for (int i = 0; i < block_num; i++) tmp2[i] = -1;
                tmp2[expression[index].value] = 1;
                dims_tmp.push_back(newPair(blocks[expression[index].value].height, blocks[expression[index].value].width, tmp2));
            }
            
            Tile *tile = new Tile(to_string(expression[index].value), dims_tmp);
            npeElems.push_back(tile);
        } else {
            vector<newPair> dims_tmp;
            string str = (expression[index].value == H) ? "H" : "V";
            
            Tile *tile = new Tile(str, dims_tmp);
            npeElems.push_back(tile);
        }
    }
    
    return npeElems;
}

// According to the OPERATOR to create all possible combination of left_node and right_node, and delete the combinations that certainly will fail.
void processStack(Tile* i, Tile* j, Tile* opr) {
    vector<newPair>::iterator dimIter1;
    vector<newPair>::iterator dimIter2;
        
    for (dimIter1 = (i->dims).begin(); dimIter1 != (i->dims).end(); dimIter1++) {
        int width_1 = (*dimIter1).width;
        int height_1 = (*dimIter1).height;
        
        for (dimIter2 = (j->dims).begin(); dimIter2 != (j->dims).end(); dimIter2++) {
            int width_2 = (*dimIter2).width;
            int height_2 = (*dimIter2).height;
            int newWidth = 0;
            int newHeight = 0;
            
            if (opr->index == "H") {
                newWidth = max(width_1, width_2);
                newHeight = height_1 + height_2;
            } else {
                newWidth = width_1 + width_2;
                newHeight = max(height_1, height_2);
            }
            
            int* tmp_array = new int[block_num];
            
            for (int i = 0; i < block_num; i++) tmp_array[i] = -1;
            
            for (int i = 0 ; i < block_num; i++) {
                if ((*dimIter1).rotate_array[i] != -1)
                    tmp_array[i] = (*dimIter1).rotate_array[i];
                
                if ((*dimIter2).rotate_array[i] != -1)
                    tmp_array[i] = (*dimIter2).rotate_array[i];
            }
            
            newPair tmp = newPair(newWidth, newHeight, tmp_array);
            (opr->dims).push_back(tmp);
        }
    }
    
    for (dimIter1 = (i->dims).begin(); dimIter1 != (i->dims).end(); dimIter1++) {
        int* tmp = (*dimIter1).rotate_array;
        delete tmp;
    }
    
    for (dimIter2 = (j->dims).begin(); dimIter2 != (j->dims).end(); dimIter2++) {
        int* tmp = (*dimIter2).rotate_array;
        delete tmp;
    }
    
    // We need to delete some combination which will certainly waste more space
    vector<newPair>::iterator dIter1;
    vector<newPair>::iterator dIter2;
    for (dIter1 = (opr->dims).begin(); dIter1 != (opr->dims).end(); dIter1++) {
        int w1 = (*dIter1).width;
        int h1 = (*dIter1).height;
        for (dIter2 = dIter1 + 1; dIter2 != (opr->dims).end(); dIter2++) {
            int w2 = (*dIter2).width;
            int h2 = (*dIter2).height;
            if (w1 >= w2 && h1 >= h2) {
                delete (*dIter1).rotate_array;
                dIter1 = (opr->dims).erase(dIter1); // erase will free memory or not
                dIter1--;
                break;
            }
            
            if(w2 >= w1 && h2 >= h1) {
                delete (*dIter2).rotate_array;
                dIter2 = (opr->dims).erase(dIter2);
                dIter2--;
            }
        }
    }
}

void updateRotate(int* rotate_array) {
    for (int i = 0; i < block_num; i++) {
        blocks[i].rotate = rotate_array[i];
    }
}

// This function will calculate wirelength of current solution
void cal_wire_length() {
    wire_length = 0;
    int max_x, min_x, max_y, min_y;
    
    for(int i = 0; i < net_num; ++i){
        max_x = 0;
        min_x = 1000000;
        max_y = 0;
        min_y = 1000000;
        
        for(auto m = net_array[i].block_list.begin(); m != net_array[i].block_list.end(); ++m) {
            int width_delta = (blocks[*m].rotate == 0) ? blocks[*m].width / 2 : blocks[*m].height / 2;
            int height_delta = (blocks[*m].rotate == 0) ? blocks[*m].height / 2 : blocks[*m].width / 2;
            int tmp_x = blocks[*m].x_coordinate + width_delta;
            int tmp_y = blocks[*m].y_coordinate + height_delta;
            if (tmp_x > max_x) max_x = tmp_x;
            if (tmp_x < min_x) min_x = tmp_x;
            if (tmp_y > max_y) max_y = tmp_y;
            if (tmp_y < min_y) min_y = tmp_y;
        }
        
        for(auto n = net_array[i].terminal_list.begin(); n != net_array[i].terminal_list.end(); ++n){
            int tmp_x = terminal_array[(*n)-1].x_coordinate;
            int tmp_y = terminal_array[(*n)-1].y_coordinate;
            if (tmp_x > max_x) max_x = tmp_x;
            if (tmp_x < min_x) min_x = tmp_x;
            if (tmp_y > max_y) max_y = tmp_y;
            if (tmp_y < min_y) min_y = tmp_y;
        }
        
        wire_length += ((max_x - min_x) + (max_y - min_y));
    }
    
    return;
}

int updateBlocksCoordinate(vector<tree_node> expression) { // update new x and y - coordinate to the blocks according to the current expression
    // This function first constructs the floorplan according to the expression
    // And then utilizes the function cal_final_wirelength to calculate the total wirelength
    // Value of the tree_node vector is treated as index of the blocks array
    // Uses header <algorithm>
    
    stack<ConstructBlock> c_blocks;
    ConstructBlock block_1, block_2;

    // Initialize the coordinates of the blocks
    for (int i = 0; i < block_num; i++) {
        blocks[i].x_coordinate = 0;
        blocks[i].y_coordinate = 0;
    }

    // Parse the expression to adjust the coordinates of blocks
    for (const auto &expr : expression) {
        if (expr.node_type == OPERAND) {                                // Node is operand
            c_blocks.push(ConstructBlock(expr.value));                  // Push a new block into stack
        } else {                                                        // Node is operator
            if (c_blocks.size() < 2) return -1;
            block_2 = c_blocks.top();                                   // Pop two blocks
            c_blocks.pop();
            block_1 = c_blocks.top();
            c_blocks.pop();

            if (expr.value == H) {                                      // Merge blocks, horizontally split (UP-DOWN)
                for (const auto &idx : block_2.block_ids) {
                    blocks[idx].y_coordinate += block_1.height;
                    block_1.block_ids.insert(idx);
                }

                block_1.height += block_2.height;
                block_1.width = max(block_1.width, block_2.width);
            } else {                                                    // Merge blocks, vertically split (LEFT-RIGHT)
                for (const auto &idx : block_2.block_ids) {
                    blocks[idx].x_coordinate += block_1.width;
                    block_1.block_ids.insert(idx);
                }

                block_1.width += block_2.width;
                block_1.height = max(block_1.height, block_2.height);
            }
            
            c_blocks.push(block_1);                                     // Push the merged block into stack
        }
    }

    cal_wire_length();                                              // Utilize the calculate wirelength function
    
    return wire_length;
}

// Calcuate the max rectangular area based on current expression
int cal_area(vector<tree_node> expression) {
    vector<Tile *> npeElems = createNPE(expression);
    stack<Tile *> npeStack;
    vector<Tile *>::iterator tileIter = npeElems.begin();

    for (; tileIter != npeElems.end(); tileIter++) {
        Tile *tile = *tileIter;
        if(tile->index != "H" && tile->index != "V") {
            npeStack.push(tile);
        } else {
            if (npeStack.empty()) return -1;
            Tile *i = npeStack.top();
            npeStack.pop();
            if (npeStack.empty()) {
                i->dims.clear();
                delete i;
                return -1;
            }
            Tile *j = npeStack.top();
            npeStack.pop();
            processStack(i, j, tile);
            i->dims.clear();
            j->dims.clear();
            delete i;
            delete j;
            npeStack.push(tile);
        }
    }
    
    Tile *stackTop = npeStack.top();

    vector<newPair>::iterator dimIter = (stackTop->dims).begin();
    int area = 0, min = INT_MAX;
    
    for ( ; dimIter != (stackTop->dims).end(); dimIter++) {
                        
        if ((*dimIter).width > floorplanning_outline && (*dimIter).height <= floorplanning_outline) {
            area = ((*dimIter).width - floorplanning_outline) * floorplanning_outline;
        } else if ((*dimIter).width <= floorplanning_outline && (*dimIter).height > floorplanning_outline) {
            area = ((*dimIter).height - floorplanning_outline) * floorplanning_outline;
        } else if ((*dimIter).width > floorplanning_outline && (*dimIter).height > floorplanning_outline) {
            area = (*dimIter).width * (*dimIter).height - floorplanning_outline * floorplanning_outline;
        } else {
            area = 0;
        }
        
        if(area < min) {
            if (area == 0) {
                updateRotate((*dimIter).rotate_array);
                updateBlocksCoordinate(expression);
                best_width = (*dimIter).width;
                best_height = (*dimIter).height;
                return area;
            }
            
            min = area; // find the best solution based on current polish expression
        }
    }
    
    for (int i = 0; i < npeElems.size(); i++) {
        npeElems[i] = nullptr;
        delete npeElems[i];
    }
    
    npeElems.clear();
    npeElems.shrink_to_fit();
    
    while (!npeStack.empty()) {
        Tile * tmp = npeStack.top();
        npeStack.pop();
        delete tmp;
    }
    
    return area;
}

bool isSkewed(vector<tree_node> expression, int pos) {
    if(expression[pos].node_type == OPERAND && pos != expression.size() - 1) {
        if(expression[pos - 1].node_type == OPERATOR && expression[pos + 1].node_type == OPERATOR && expression[pos - 1].value == expression[pos + 1].value)
            return false;
        else
            return true;
    } else if (expression[pos].node_type == OPERATOR && pos > 1) {
        if(expression[pos].node_type == OPERATOR && expression[pos + 2].node_type == OPERATOR && expression[pos].value == expression[pos + 2].value)
            return false;
        else
            return true;
    } else
        return false;
}

bool isBalloting(vector<tree_node> expression, int index) {
    int count = 0;
    
    if (expression[index + 1].node_type == OPERATOR) {
        for (int i = 0; i <= index + 1; i++)
            if (expression[i].node_type == OPERATOR) count++;
        
        if (count * 2 < index + 1) return true;
        else return false;
    }
    
    return true;
}

// Compress all blocks in the target region, so that we can save lots of time to calculate
vector<tree_node> initialExpr(vector<tree_node> expression) {
    expression.clear();
    int row_width = 0, x_cnt = 0, y_cnt = 0, cut_cnt = 0;
    for(int i = 0; i < block_num; i ++) {
        row_width += blocks[i].width;
        if(row_width >= floorplanning_outline) {
            y_cnt++;
            if(y_cnt >= 2) {
                tree_node cut = tree_node(OPERATOR, H);
                expression.push_back(cut);
                cut_cnt++;
                y_cnt = 1;
            }
            row_width = blocks[i].width;
            x_cnt = 0;
        }
        expression.push_back(tree_node(OPERAND, i));
        x_cnt++;
        if(x_cnt >= 2) {
            tree_node cut = tree_node(OPERATOR, V);
            expression.push_back(cut);
            cut_cnt++;
            x_cnt = 1;
        }
    }
    while(cut_cnt < block_num - 1) {
        tree_node cut = tree_node(OPERATOR, H);
        expression.push_back(cut);
        cut_cnt++;
    }
    return expression;
}

vector<tree_node> perturb(vector<tree_node> expression, int op) {
    int node_1, node_2 = 0;
    unsigned long int expr_len = expression.size();
    switch (op) {
        case 0: {     // swap two adjacent operands
            int *buffer = new int[expr_len];
            int count = 0;
                            
            for (int i = 0; i < expr_len; i++) {
                if (expression[i].node_type == OPERAND)
                    buffer[count++] = i;
            }
                            
            node_1 = rand() % (count - 1); //  count - 1 can prevent we find last index of expression, so that we don't need to
            node_2 = rand() % (count - 1); //  check whether the index will exceed the length of expression
                            
            while (node_1 == node_2)
                node_2 = rand() % (count - 1);
                                        
            swap(expression[buffer[node_1]], expression[buffer[node_2]]);
            delete[] buffer;
        } break;
        case 1: {     // Complement a chain
            int *buffer = new int[expr_len];
            int count = 0;
                            
            for (int i = 1; i < expr_len; i++)
                if (expression[i].node_type == OPERATOR && expression[i - 1].node_type == OPERAND) buffer[count++] = i;
                            
            node_1 = invert_index = buffer[rand() % count];
                            
            while (expression[node_1].node_type == OPERATOR && node_1 < expr_len) {
                expression[node_1].value = (expression[node_1].value == H) ? V : H;
                node_1++;
            }
            delete[] buffer;
        } break;
            case 2: {     // Swap two adjacent operand and operator
                int *buffer = new int[expr_len];
                int count = 0;
                int invalid_count = 0;
                            
                for (int i = 0; i < expr_len - 1; i++) {
                    if ((expression[i].node_type == OPERATOR && expression[i + 1].node_type == OPERAND) || (expression[i].node_type == OPERAND && expression[i + 1].node_type == OPERATOR)) buffer[count++] = i;
                }
                            
                node_1 = rand() % count;
                            
                do {
                    node_1 = rand() % count;
                    invalid_count++;
                } while(invalid_count < count && !isBalloting(expression, buffer[node_1]) && isSkewed(expression, buffer[node_1]));
                            
                if(invalid_count < count)
                    swap(expression[buffer[node_1]], expression[buffer[node_1] + 1]);
                        
                delete[] buffer;
        } break;
    }
    return expression;
}

void schedule_annealling(float p, double eps, double reduce, int k) {
    int MT = 0, uphill = 0, reject = 0;
    int current_cost = 0, tmp_cost = 0, best_cost = 0, delta_cost;
    double temperature = 10000; // the meaning of the word is not the one we think, in this function, its meaning is close to "stability"
    unsigned long int expr_len;
    bool find = false;
    
    // Polish Expression
    vector<tree_node> expr;
    vector<tree_node> expr_tmp;
    vector<tree_node> expr_best;
    
    expr = initialExpr(expr);
    
    expr_best = expr;
    best_cost = current_cost = cal_area(expr);
    expr_len = expr.size();
    
    if (current_cost == 0) find = true;
    
    do {
        do {
            MT = uphill = reject = 0;
            while (uphill <= k && MT <= 2 * k) {
                int op = rand() % 3;
                expr_tmp = perturb(expr, op);
                tmp_cost = cal_area(expr_tmp);
                MT++;
                delta_cost = tmp_cost - current_cost;
                if (tmp_cost >= 0) {
                    if(delta_cost < 0 || (double)rand() / RAND_MAX < exp(-1 * delta_cost / temperature)) {
                        
                        if (delta_cost > 0) {
                            uphill++;
                        } else { // if coat decreased, then print update expr, and print out
                            current_cost = tmp_cost;
                            expr = expr_tmp;
                            //cout << tmp_cost << " " << op << endl;
                        }
                        
                        if(current_cost < best_cost) {
                            best_cost = current_cost;
                            expr_best = expr;
                            if(best_cost == 0) { //  final floor plan constraited in floorplanningOutlin^2
                                find = 1;
                                break;
                            }
                        }
                    } else {
                        if (op == 1) {
                            // reverse the operation 1
                            while (expr_tmp[invert_index].node_type == OPERATOR && invert_index < expr_len) {
                                expr_tmp[invert_index].value = (expr_tmp[invert_index].value == H) ? V : H;
                                invert_index++;
                            }
                        }
                        
                        reject++;
                    }
                    temperature *= temperature * reduce;
                }
            }
        } while (reject / MT <= 0.95 && temperature >= eps && !find);
        temperature = 10000;
    } while (!find);
}

// Write solution to .output file
void writeSolution(FILE* file) {
    fprintf(file, "Wirelength %d\n", wire_length);
    fprintf(file, "Blocks\n");
    
    for(int i = 0; i < block_num; ++i)
        fprintf(file, "sb%d %d %d %d\n", i, blocks[i].x_coordinate, blocks[i].y_coordinate, blocks[i].rotate);
    
    return;
}

int main(int argc, const char * argv[]) {
    // read or write file
    block_file = fopen("n300.blocks", "r");
    net_file = fopen("n300.nets", "r");
    terminal_file = fopen("n300.pl", "r");
    solution_file = fopen("n300.output", "w");
    
    // fetching data from files and closed them
    readBlock(block_file);
    fclose(block_file);
    readNets(net_file);
    fclose(net_file);
    readTerminal(terminal_file);
    fclose(terminal_file);
    
    double wall0 = get_wall_time();
    double cpu0  = get_cpu_time();
    
    srand(4);
    cout << "block: " << block_num << endl;
    cout << "area: " << total_area << endl;
    floorplanning_outline = (int)sqrt(total_area * (1 + dead_ratio));  // outline of the region according to the dead ratio
    cout << "dead_ratio: " << dead_ratio << " floorplanning_outline: " << floorplanning_outline << endl;
    schedule_annealling(0.98, 0.001, 0.85, 10);
    
    cout << best_width << " " << best_height << endl;
    
    double wall1 = get_wall_time();
    double cpu1  = get_cpu_time();
    
    cout << "\nTime(s) : Simulated Annealing : Wall Time : " << wall1 - wall0 << ", CPU Time : " << cpu1  - cpu0 << std::endl;
    
    // output process
    writeSolution(solution_file);
    fclose(solution_file);
    
    return 0;
}
